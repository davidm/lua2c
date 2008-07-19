-- lua2c - convert Lua source to C code.
--
-- WARNING: This code is under development.  A number of
-- things may be broken/unimplemented at this time.
-- A few things (upvalues/coroutines/tail calls) might remain
-- unimplemented--see README file file for details.
--
-- (c) 2008 David Manura.  Licensed under the same terms as Lua (MIT license).

package.path = package.path .. ';./lib/?.lua'


-- gg/mlp Lua parsing Libraries from Metalua.
require "lexer"
require "gg"
require "mlp_lexer"
require "mlp_misc"
require "mlp_table"
require "mlp_meta"
require "mlp_expr"
require "mlp_stat"
require "mlp_ext"


-- http://lua-users.lua.org/wiki/DetectingUndefinedVariables
if checkglobals then checkglobals() end

local format = string.format


--
-- SECTION: Converts Lua source string to Lua AST (via mlp/gg)
--

local mlc = { } 
_G.mlc = mlc   -- make visible to mlp modules.

function mlc.ast_of_luastring (src)
  local  lx  = mlp.lexer:newstream (src)
  local  ast = mlp.chunk (lx)
  return ast
end

--[[UNUSED
function mlc.function_of_luastring (src)
  local  ast  = mlc.ast_of_luastring (src)
  local  func = mlc.function_of_ast(ast)
  return func
end
--]]

--[[UNUSED
function mlc.function_of_luafile (name)
  local f   = io.open(name, 'r')
  local src = f:read '*a'
  f:close()
  return mlc.function_of_luastring (src, "@"..name)
end
--]]


--
-- SECTION: Converts Lua ASTs to C ASTs.
--
-- Variable naming conventions: ast (Lua AST), cast (C AST).
--


-- Lua code string currently converting.
local src


-- topmost stack index
local idxtop = 0

-- Table of local variables.
-- Maps name -> stack index
local localvars = {}



-- Builds set from elements in array t.
local function makeset(t)
  local set = {}
  for _,v in ipairs(t) do set[v] = true end
  return set
end


-- Set of identifiers of binary operators
-- (metamethod name without "__" prefix).
local is_binopid = makeset {
  "add",   "sub", "mul",    "div",
  "mod",   "pow", "concat", "eq",
  "lt",    "le",  "and",    "or"
}

-- Set of identifiers of unary operators.
local is_unopid = makeset {
  "not", "len", "unm"
}

-- Set of binary ops with metamethod behavior like "+".
local is_arithbinop = makeset {
  "add", "sub", "mul", "div", "mod", "pow"
}

-- Maps operator identifier to function
-- implementing that identifier (without metamethods).
local fops = {
  ["add"]   =function(a,b) return a+b end,
  ["sub"]   =function(a,b) return a-b end,
  ["mul"]   =function(a,b) return a*b end,
  ["div"]   =function(a,b) return a/b end,
  ["mod"]   =function(a,b) return a%b end,
  ["pow"]   =function(a,b) return a^b end,
  ["concat"]=function(a,b) return a..b end,
  ["eq"]    =function(a,b) return a==b end,
  ["lt"]    =function(a,b) return a<b end,
  ["le"]    =function(a,b) return a<=b end,
  ["and"]   =function(a,b) return a and b end,
  ["or"]    =function(a,b) return a or b end,
  ["not"]   =function(a)   return not a end,
  ["len"]   =function(a)   return #a end,
  ["unm"]   =function(a)   return -a end
}

-- Maps operator identifier to function that returns
-- a C code string implementing that identifier
-- (without metamethods).
local opid_to_c = {
  ["add"]=function(a,b) return a .. ' + ' .. b end,
  ["sub"]=function(a,b) return a .. ' - ' .. b end,
  ["mul"]=function(a,b) return a .. ' * ' .. b end,
  ["div"]=function(a,b) return a .. ' / ' .. b end,
  ["mod"]=function(a,b) return
            a .. ' - floor(' .. a .. '/' .. b ..')*' .. b end,
          -- caution: a and b evaluate twice
  ["pow"]=function(a,b) return 'pow(' .. a .. ',' .. b .. ')' end,
          --FIX:include math.h
  --["concat"]=function(a,b) return FIX end,
  --["eq"]=function(a,b) return FIX end,
  --["lt"]=function(a,b) return FIX end,
  --["le"]=function(a,b) return FIX end,
  --["and"]=function(a,b) return FIX end,
  --["or"]=function(a,b) return FIX end,
  --["not"] = function(a) return FIX end,
  --["len"] = function(a) return FIX end,
  --["unm"] = function(a) return FIX end
}

-- Converts Lua object to Lua AST.
local function obj_to_ast(obj)
  if obj == nil then
    return {tag='Nil'}
  elseif obj == true then
    return {tag='True'}
  elseif obj == false then
    return {tag='False'}
  elseif type(obj) == 'number' then
    return {tag='Number', obj}
  elseif type(obj) == 'string' then
    return {tag='String', obj}
  else
    assert(false, 'FIX:NOT IMPL:' .. tostring(obj))
  end
end


-- Appends elements to array t2 to array t1.
local function append_array(t1,t2)
  for _,v in ipairs(t2) do t1[#t1+1] = v end
end

local function append_cast(cast1, cast2)
  if cast2.tag ~= nil then -- enclosing block omitted (convenience)
    assert(not cast2.pre)
    assert(not cast2.idx)
    cast2 = {cast2, pre=cast2.pre or {}, idx=nil}
  end
  append_array(cast1, cast2)
  append_array(cast1.pre, cast2.pre)
  return cast2  --FIX:ok?
end


-- Constructor and type for C AST nodes.
local cexpr_mt = {}
cexpr_mt.__index = cexpr_mt
function cexpr_mt:append(cast)
  return append_cast(self, cast)
end
local function cexpr(...)
  return setmetatable({idx=-1, pre={}, ...}, cexpr_mt)
end

local C_mt = {}
function C_mt.__index(t,k,v)
  local f = function(...) return {tag=k, ...} end
  t.k = f -- cache
  return f
end
local C = setmetatable({}, C_mt)



-- Adjusts stack index to relative (negative) position offset.  note:
-- use only when values inside offset are on the stack
-- (non-psuedoindices)
local function adjustidx(offset, idx)
  if idx > 0 then
    return idx
  else -- relative stack index or pseudoindex
     -- FIX:pseudoindices not supported
    return idx + offset + 1
  end
end

-- Adjusts relative stack indicies
local function adjustidxs(...)
  local nused = 0
  local result = {...}
  for i=#result,1,-1 do
    local idx = result[i]
    if idx < 0 then  --FIX: and idx > LUA_REGISTRYINDEX ?
      result[i] = result[i] - nused
    end
    if idx == -1 then
      nused = nused + 1
    end
  end
  return unpack(result)
end

-- Counts number of temporary values on stack.
local function countstack(...)
  local n = select('#', ...)
  local ncount = 0
  for i=1,n do
    local idx = select(i, ...)
    if idx == -1 then ncount = ncount + 1 end
  end
  return ncount
end


-- Gets range of line numbers (first,last) represented by AST
-- returns nothing if not information found.
-- IMPROVE:hack.  Does gg/mlp already provide this?
local function linerange(ast)
  if ast.lineinfo then
    return ast.lineinfo.first, ast.lineinfo.last
  end
  local first, last
  for i,ast2 in ipairs(ast) do
    if type(ast2) == 'table' then
      local first2,last2 = linerange(ast2)
      if first2 and (not first or first2 < first) then
        first = first2
      end
      if last2 and (not last or last2 > last) then
        last = last2
      end
    end
  end
  if first then
    return first, last
  end
end

-- Gets string representing lines first to last in string s.
local cache
local function getlines(s, first, last)
  cache = cache or {}
  local lines = cache[s]
  if not lines then
    lines = {}
    for line in s:gmatch("([^\r\n]*)\r?\n?") do
      lines[#lines+1] = line
    end
    lines[#lines] = nil
    cache[s] = lines
  end
  local ts = {}
  for i=first,last do ts[#ts+1] = lines[i] end
  local slines = table.concat(ts, "\n")
  return slines  
end


-- Gets next unique ID.  Useful in variable names to
-- ensure uniqueness.
local _id = 0
local function nextid()
  _id = _id + 1
  return 'lc' .. _id
end


local function newscope()
  local localvars_old = localvars
  local localvars = {}
  return setmetatable(localvars, {__index = localvars_old})
end


-- Performs constant folding on AST.
local function constant_fold(ast)
  if ast.tag == 'Op' then
    local opid = ast[1]
    local a_ast = constant_fold(ast[2])
    local b_ast = ast[3] and constant_fold(ast[3])
    if b_ast then  -- binary op
      if a_ast.tag == 'Number' and b_ast.tag == 'Number' then
        return obj_to_ast(fops[opid](a_ast[1], b_ast[1]))
      end
    else  -- unary op
      if a_ast.tag == 'Number' then
        return obj_to_ast(fops[opid](a_ast[1]))
      end
    end
  end
  return ast
end


-- forward declarations
local genexpr
local genblock


-- note: is_created maps function name to boolean indicated whether
-- function has been generated.
local is_created = {}
local function genarithbinop(ast, where)
  -- Returns C AST node definition arithmetic binary op with given
  -- identitifier.
  local function makebinop(opid)
    local ccode = string.format([[
/* __%s metamethod handler.
 * warning: assumes indices in range LUA_REGISTRYINDEX < x < 0 are relative. */
static double lc_%s(lua_State * L, int idxa, int idxb) {
  if (lua_isnumber(L,idxa) && lua_isnumber(L,idxb)) {
    return %s;
  }
  else {
    if (luaL_getmetafield(L,idxa,"__%s")||luaL_getmetafield(L,idxb,"__%s")) {
      lua_pushvalue(L,idxa < 0 && idxa > LUA_REGISTRYINDEX ? idxa-1 : idxa);
      lua_pushvalue(L,idxb < 0 && idxb > LUA_REGISTRYINDEX ? idxb-2 : idxb);
      lua_call(L,2,1);
      const double result = lua_tonumber(L,-1);
      lua_pop(L,1);
      return result;
    }
    else {
      return luaL_error(L, "attempt to perform arithmetic");
    }
  }
}
]],   opid, opid,
      assert(opid_to_c[opid])("lua_tonumber(L,idxa)", "lua_tonumber(L,idxb)"),
      opid, opid)

    return C.C(ccode)
  end

  local opid, a_ast, b_ast = ast[1], ast[2], ast[3]

  local cast = cexpr()

  local fname = "lc_" .. opid
  if not is_created[fname] then
    append_array(cast.pre, {makebinop(opid)})
    is_created[fname] = true
  end

  local a_idx = cast:append(genexpr(a_ast, 'anywhere')).idx
  local b_idx = cast:append(genexpr(b_ast, 'anywhere')).idx
  local nstack = countstack(a_idx, b_idx)
  a_idx, b_idx = adjustidxs(a_idx, b_idx)
  if nstack == 0 then
    cast:append(C.lua_pushnumber(C.CallL('lc_'..opid, a_idx, b_idx)))
  else
    local id = nextid()
    cast:append(C.LetDouble(id, C.CallL('lc_'..opid, a_idx, b_idx)))
    cast:append(C.lua_pop(nstack))
    cast:append(C.lua_pushnumber(C.Id(id)))
  end

  return cast
end


local function geneqop(ast, where)
  local a_ast, b_ast = ast[2], ast[3]
  local cast = cexpr()
  local a_idx = cast:append(genexpr(a_ast, where)).idx
  local b_idx = cast:append(genexpr(b_ast, where)).idx
  local nstack = (a_idx == -1 and 1 or 0) + (b_idx == -1 and 1 or 0)
  a_idx, b_idx = adjustidxs(a_idx, b_idx)
  local id = nextid(); cast:append(C.Let(id, C.lua_equal(a_idx, b_idx)))
  if nstack ~= 0 then
    cast:append(C.lua_pop(nstack))
  end
  cast:append(C.lua_pushboolean(C.Id(id)))
  return cast
end

local function genltop(ast, where)
  local opid, a_ast, b_ast = ast[1], ast[2], ast[3]
  local cast = cexpr()

  local a_idx = cast:append(genexpr(a_ast, 'anywhere')).idx
  local b_idx = cast:append(genexpr(b_ast, 'anywhere')).idx
  local nstack = countstack(a_idx, b_idx)
  a_idx, b_idx = adjustidxs(a_idx, b_idx)

  local id = nextid(); cast:append(C.Let(id, C.lua_lessthan(a_idx, b_idx)))

  if nstack ~= 0 then
    cast:append(C.lua_pop(nstack))
  end

  cast:append(C.lua_pushboolean(C.Id(id)))

  return cast
end


-- Why does the Lua C API implement lua_lessthan but not lua_lessequal?
-- (note: lessqual is defined in lvm.c).
local function genleop(ast, where)
  local function makeop()
    local cast = C.C [[
/* warning: assumes indices in range LUA_REGISTRYINDEX < x < 0 are relative. */
static int lc_le(lua_State * L, int idxa, int idxb) {
  if (lua_type(L,idxa) == LUA_TNUMBER && lua_type(L,idxb) == LUA_TNUMBER) {
    return lua_tonumber(L,idxa) <= lua_tonumber(L,idxb);
  }
  else if (lua_type(L,idxa) == LUA_TSTRING && lua_type(L,idxb) == LUA_TSTRING) {
    /* result similar to lvm.c l_strcmp */
    return lua_lessthan(L,idxa,idxb) || lua_rawequal(L,idxa,idxb);
  }
  else if (luaL_getmetafield(L,idxa,"__le")||luaL_getmetafield(L,idxb,"__le")) {
    lua_pushvalue(L,idxa < 0 && idxa > LUA_REGISTRYINDEX ? idxa-1 : idxa);
    lua_pushvalue(L,idxb < 0 && idxb > LUA_REGISTRYINDEX ? idxb-2 : idxb);
    lua_call(L,2,1);
    const int result = lua_toboolean(L,-1);
    lua_pop(L,1);
    return result;
  }
  else if (luaL_getmetafield(L,idxa,"__lt")||luaL_getmetafield(L,idxb,"__lt")) {
    lua_pushvalue(L,idxb < 0 && idxb > LUA_REGISTRYINDEX ? idxb-1 : idxb);
    lua_pushvalue(L,idxa < 0 && idxa > LUA_REGISTRYINDEX ? idxa-2 : idxa);
    lua_call(L,2,1);
    const int result = ! lua_toboolean(L,-1);
    lua_pop(L,1);
    return result;
  }
  else {
    return luaL_error(L, "attempt to compare");
  }
}
]]

    return cast
  end

  local opid, a_ast, b_ast = ast[1], ast[2], ast[3]
  local cast = cexpr()

  local fname = "lc_le"
  if not is_created[fname] then
    append_array(cast.pre, {makeop(opid)})
    is_created[fname] = true
  end

  local a_idx = cast:append(genexpr(a_ast, 'anywhere')).idx
  local b_idx = cast:append(genexpr(b_ast, 'anywhere')).idx
  local nstack = countstack(a_idx, b_idx)
  a_idx, b_idx = adjustidxs(a_idx, b_idx)
  if nstack == 0 then
    cast:append(C.lua_pushboolean(C.CallL('lc_le', a_idx, b_idx)))
  else
    local id = nextid()
    cast:append(C.Let(id, C.CallL('lc_le', a_idx, b_idx)))
    cast:append(C.lua_pop(nstack))
    cast:append(C.lua_pushboolean(C.Id(id)))
  end

  return cast
end

local function genlogbinop(ast, where)
  local opid, a_ast, b_ast = ast[1], ast[2], ast[3]
  local cast = cexpr()

  cast:append(genexpr(a_ast, 'onstack'))

  assert(opid == 'and' or opid == 'or')
  local expr_cast = C.lua_toboolean(-1)
  if opid == 'or' then expr_cast = C.Not(expr_cast) end
  local block_cast = cexpr()
  block_cast:append(C.lua_pop(1))
  block_cast:append(genexpr(b_ast, 'onstack'))
  cast:append(C.If(expr_cast, block_cast))
  append_array(cast.pre, block_cast.pre)

  return cast
end

local function gennotop(ast, where)
  local opid, a_ast = ast[1], ast[2]
  local cast = cexpr()

  local a_idx = cast:append(genexpr(a_ast, 'anywhere')).idx

  cast:append(C.lua_pushboolean(C.Not(C.lua_toboolean(a_idx))))
  if a_idx == -1 then
    cast:append(C.lua_remove(-2))
  end

  return cast
end


local function genconcatop(ast, where)
  local a_ast, b_ast = ast[2], ast[3]
  local cast = cexpr()

  cast:append(genexpr(a_ast, 'onstack'))
  cast:append(genexpr(b_ast, 'onstack'))
  cast:append(C.lua_concat(2))

  return cast
end

local function genfunction(ast, where)
  local params_ast, body_ast = ast[1], ast[2]
  local cast = cexpr()

  --## generate function definition

  -- localize code
  local localvars_save = localvars  --FIX:how to handle upvalues?
  local idxtop_old = idxtop
  idxtop = 0   -- FIX: currently assuming no upvalues
  localvars = {}

  for i,var_ast in ipairs(params_ast) do
    assert(var_ast.tag ~= 'Dots', 'FIX:NOT IMPL: dots ...')
    assert(var_ast.tag == 'Id')
    local varname = var_ast[1]
    localvars[varname] = i
    idxtop = idxtop + 1
  end

  local body_cast = cexpr(); body_cast.pre = cast.pre
  local id = nextid() .. '_func'  -- IMPROVE: deduce function name
  body_cast:append(genblock(body_ast))
  if #body_ast > 0 and body_ast[#body_ast].tag ~= 'Return' then
    body_cast:append(C.Return(0))
  end
  local def_cast = C.Functiondef(id, body_cast)
  def_cast.comment = getlines(src, linerange(ast))
  append_array(cast.pre, {def_cast})

  localvars = localvars_save
  idxtop = idxtop_old

  --## generate function object
  cast:append(C.lua_pushcfunction(C.Id(id)))

  return cast
end

local function gentable(ast, where)
  local cast = cexpr()
  local narr = 0
  local nrec = 0
  for _,e_ast in ipairs(ast) do
    if e_ast.tag == 'Pair' then    -- Q: always true?
      nrec = nrec + 1
    else
      narr = narr + 1
    end
  end
  if narr + nrec == 0 then
    cast:append(C.lua_newtable())
  else
    cast:append(C.lua_createtable(narr,nrec))
  end

  local pos = 0
  for _,e_ast in ipairs(ast) do
    if e_ast.tag == 'Pair' then
      local k_ast, v_ast = e_ast[1], e_ast[2]
      cast:append(genexpr(k_ast, 'onstack'))
      cast:append(genexpr(v_ast, 'onstack'))
      cast:append(C.lua_rawset(-3))
    else
      cast:append(genexpr(e_ast, 'onstack'))
      pos = pos + 1
      cast:append(C.lua_rawseti(-2, pos))
    end
  end
  return cast
end

local function gencall(ast, where, nret)
  local isinvoke = ast.tag == 'Invoke'
  local iarg = isinvoke and 3 or 2
  local cast = cexpr()

  -- whether last argument might possibly return multiple values
  local can_multret = #ast >= iarg and
    (ast[#ast].tag == 'Call' or ast[#ast].tag == 'Invoke')

  local id
  local function f()
    if can_multret then
      id = nextid(); cast:append(C.Let(id, C.lua_gettop()))
    end
  end

  if isinvoke then
    local expr_ast, name_ast = ast[1], ast[2]  -- ...
    cast:append(genexpr(expr_ast, 'onstack'))
    f()
    cast:append(genexpr(name_ast, 'onstack'))
    cast:append(C.lua_gettable(-2))
    cast:append(C.lua_insert(-2))
  else
    assert(ast.tag == 'Call')
    local f_ast = ast[1]
    cast:append(genexpr(f_ast, 'onstack'))
    f()
  end

  for i=iarg,#ast do
    local ast2 = ast[i]
    cast:append(genexpr(ast2, 'onstack', i == #ast and 'multret' or false))
  end
  local narg = can_multret and C.Op('-', C.lua_gettop(), C.Id(id)) or #ast-1
  if nret == 'multret' then
    cast:append(C.lua_call(narg, C.C'LUA_MULTRET'))
  else
    cast:append(C.lua_call(narg, nret or 1))
  end
  return cast
end

-- local
function genexpr(ast, where, nret)
  if ast.tag == 'Op' then
    ast = constant_fold(ast)
  end

  if ast.tag == 'Nil' then
    return cexpr(C.lua_pushnil())
  elseif ast.tag == 'Dots' then
    assert(false, 'FIX:NOT IMPL: dots ...')
  elseif ast.tag == 'True' then
    return cexpr(C.lua_pushboolean(1))
  elseif ast.tag == 'False' then
    return cexpr(C.lua_pushboolean(0))
  elseif ast.tag == 'Number' then
    return cexpr(C.lua_pushnumber(ast[1]))
  elseif ast.tag == 'String' then
    local s = ast[1]
    return cexpr(C.lua_pushliteral(s))
  elseif ast.tag == 'Function' then
    return genfunction(ast, where)
  elseif ast.tag == 'Table' then
    return gentable(ast, where)
  elseif ast.tag == 'Op' then
    local opid = ast[1]
    if is_binopid[opid] then
      if is_arithbinop[opid] then
        return genarithbinop(ast, where)
      elseif opid == 'eq' then
        return geneqop(ast, where)
      elseif opid == 'lt' then
        return genltop(ast, where)
      elseif opid == 'le' then
        return genleop(ast, where)
      elseif opid == 'or' or opid == 'and' then
        return genlogbinop(ast, where)
      elseif opid == 'concat' then
        return genconcatop(ast, where)
      else
        error('FIX:NOT-IMPL:' .. opid)
      end
    elseif is_unopid[opid] then
      if opid == 'not' then
        return gennotop(ast, where)
      else
        error('FIX:NOT-IMPL:' .. opid)
      end
    else
      assert(false, opid)
    end
  elseif ast.tag == 'Paren' then
    local ast2 = ast[1]
    return genexpr(ast2, where)
  -- note: metalua allows `Stat here too as an extension
  elseif ast.tag == 'Call' or ast.tag == 'Invoke' then
    return gencall(ast, where, nret)
  elseif ast.tag == 'Id' then
    local name = ast[1]
    local cast = cexpr()
    if localvars[name] then -- local
      local idx = localvars[name]
      if where == 'anywhere' then
        cast.idx = idx
        return cast
      else
        cast:append(C.lua_pushvalue(idx))
      end
    else -- global
      cast:append(C.lua_getglobal(name))
    end
    return cast
  elseif ast.tag == 'Index' then
    local cast = cexpr()
    local t_ast, k_ast = ast[1], ast[2]
    local t_idx = cast:append(genexpr(t_ast, 'anywhere')).idx
    cast:append(genexpr(k_ast, 'onstack'))
    cast:append(C.lua_gettable(adjustidx(-2, t_idx)))
    if t_idx == -1 then
      cast:append(C.lua_remove(-2))
    end
    return cast
  else
    assert(false, ast.tag)
  end
end


local function genlvalueassign(l_ast)
  local cast = cexpr()
  if l_ast.tag == 'Id' then
    local name = l_ast[1]
    if localvars[name] then
      local l_idx = localvars[name]
      cast:append(C.lua_replace(l_idx))
    else  -- global
      cast:append(C.lua_setglobal(name))
    end
  elseif l_ast.tag == 'Index' then
    local t_ast, k_ast = l_ast[1], l_ast[2]
    local t_idx = cast:append(genexpr(t_ast, 'anywhere')).idx
    if t_idx == -1 then cast:append(C.lua_insert(-2)) end
    cast:append(genexpr(k_ast, 'onstack'))
    cast:append(C.lua_insert(-2))
    cast:append(C.lua_settable(adjustidx(-3, t_idx)))
    if t_idx == -1 then
      cast:append(C.lua_pop(1))
    end
  else
    assert(false, l_ast.tag)
  end
  return cast
end


local function genif(ast)
  local cast = cexpr()
  local if_args = {pre=cast.pre}

  local a_idx = cast:append(genexpr(ast[1], 'anywhere')).idx
  if a_idx ~= -1 then
    if_args[1] = C.lua_toboolean(a_idx)
  else
    local id = nextid();
    cast:append(C.Let(id, C.lua_toboolean(-1)))
    cast:append(C.lua_pop(1))
    if_args[1] = C.Id(id)
  end

  local localvars_save = localvars
  localvars = newscope()
  local block_cast = genblock(ast[2])
  table.insert(if_args, block_cast)
  append_array(cast.pre, block_cast.pre)
  localvars = localvars_save

  if #ast == 2 then
  elseif #ast == 3 then
    local localvars_save = localvars
    localvars = newscope()
    local block_cast = genblock(ast[3])
    table.insert(if_args, block_cast)
    append_array(cast.pre, block_cast.pre)
    localvars = localvars_save
  else
    assert(false, 'FIX:NOT IMPL: elseif')
  end

  cast:append(C.If(unpack(if_args)))

  return cast
end


-- Converts Lua `Fornum AST to C AST.
local function genfornum(ast)
  local name_ast, e1_ast, e2_ast, e3_ast, block_ast =
    ast[1], ast[2], ast[3], ast[5] and ast[4] or ast[5], ast[5] or ast[4]
  local name_id = name_ast[1]; assert(name_ast.tag == 'Id')
  local cast = cexpr()

  local var_id = nextid();
  local limit_id = nextid();
  local step_id = nextid();
  local var_idx = cast:append(genexpr(e1_ast, 'anywhere')).idx
  local limit_idx = cast:append(genexpr(e2_ast, 'anywhere')).idx
  local step_idx = e3_ast and cast:append(genexpr(e3_ast, 'anywhere')).idx

  local nstack = (var_idx   == -1 and 1 or 0) +
                 (limit_idx == -1 and 1 or 0) +
                 (step_idx  == -1 and 1 or 0)

  var_idx, limit_idx, step_idx = adjustidxs(var_idx, limit_idx, step_idx)


  local expr_cast =
    C.Op('&&', C.lua_isnumber(var_idx), C.lua_isnumber(limit_idx))
  if step_idx then
    expr_cast = C.Op('&&', expr_cast, C.lua_isnumber(step_idx))
  end  
  cast:append(
    C.If(C.Not(expr_cast),
         {C.CallL('luaL_error', "'for' limit must be a number")}))
  cast:append(C.LetMutableDouble(var_id, C.lua_tonumber(var_idx)))
  cast:append(C.LetDouble(limit_id, C.lua_tonumber(limit_idx)))
  if e3_ast then
    cast:append(C.LetDouble(step_id, C.lua_tonumber(step_idx)))
  else
    cast:append(C.LetDouble(step_id, 1.0))
  end

  cast:append(C.lua_pop(nstack))

  local while_expr_cast =
    C.Op('||',
      C.Op('&&',
        C.Op('>', C.Id(step_id), 0),
        C.Op('<=', C.Id(var_id), C.Id(limit_id))),
      C.Op('&&',
        C.Op('<=', C.Id(step_id), 0),
        C.Op('>=', C.Id(var_id), C.Id(limit_id))))

  -- local scope to evaluate block
  local localvars_save = localvars
  localvars = newscope()
  local var_absidx = idxtop + 1
  localvars[name_id] = var_absidx

  local block_cast = cexpr()
  block_cast:append(C.lua_pushnumber(C.Id(var_id)))
  block_cast[1].comment =
   string.format("internal: local %s at index %d", name_id, var_absidx)
  idxtop = idxtop + 1
  block_cast:append(genblock(block_ast))
  block_cast:append(C.lua_pop(1))
  idxtop = idxtop - 1
  localvars = localvars_save

  block_cast:append(C.C(var_id .. ' += ' .. step_id .. ';')) --IMPROVE?
  cast:append(C.While(while_expr_cast, block_cast))
  append_array(cast.pre, block_cast.pre)
  return cast
end

-- Returns whether expression could possibly return a number of argument
-- different from 1.
-- note: expr_ast can be nil
local function can_multi(expr_ast)
  return expr_ast and (expr_ast.tag == 'Call' or expr_ast.tag == 'Invoke')
end


-- Converts Lua `Forin AST to C AST.
local function genforin(ast)
  local names_ast, exprs_ast, block_ast = ast[1], ast[2], ast[3]
  local cast = cexpr()

  local multi = can_multi(exprs_ast[1])

  local nlast = multi and 3 + 1 - #exprs_ast or 1
  for i,expr_ast in ipairs(exprs_ast) do
    cast:append(genexpr(expr_ast, 'onstack',
      i==#exprs_ast and math.max(0,nlast)))
  end
  if nlast < 0 then
    cast:append(C.lua_pop(-nlast))
  end

  idxtop = idxtop + 3

  local id = nextid(); cast:append(C.Let(id, C.lua_gettop()))


  local block_cast = cexpr()

  block_cast:append(C.lua_settop(C.Id(id)))

  -- local scope to evaluate block
  local localvars_save = localvars
  localvars = newscope()
  for _,name_ast in ipairs(names_ast) do
    local name_id = name_ast[1]; assert(name_ast.tag == 'Id')
    idxtop = idxtop + 1
    localvars[name_id] = idxtop
  end

  block_cast:append(C.lua_pushvalue(-3))
  block_cast:append(C.lua_pushvalue(-3))
  block_cast:append(C.lua_pushvalue(-3))
  block_cast:append(C.lua_call(2,#names_ast))
  for i,name_ast in ipairs(names_ast) do
    block_cast[#block_cast].comment =
      string.format("internal: local %s at index %d",
                    name_ast[1], idxtop - #names_ast + i)
  end

  block_cast:append(C.If(C.lua_isnil(- #names_ast), {C.Break()}))

  block_cast:append(C.lua_pushvalue(- #names_ast))
  block_cast:append(C.lua_replace(- #names_ast - 2))

  block_cast:append(genblock(block_ast))

  idxtop = idxtop - 1
  localvars = localvars_save

  cast:append(C.While(1, block_cast))
  append_array(cast.pre, block_cast.pre)

  cast:append(C.lua_settop(C.Op('-', C.Id(id), 3)))

  idxtop = idxtop - 3

  return cast
end


-- Converts Lua `While AST to C AST.
local function genwhile(ast)
  local expr_ast, block_ast = ast[1], ast[2]
  local cast = cexpr()
  local id = nextid(); cast:append(C.Let(id, C.lua_gettop()))

  do
    local block_cast = cexpr()
    local expr_idx = block_cast:append(genexpr(expr_ast, 'anywhere')).idx

    block_cast:append(
      C.If(C.Not(C.lua_toboolean(expr_idx)),
           expr_idx == -1 and {C.lua_pop(1), C.Break()} or {C.Break()}))
    block_cast:append(C.lua_pop(1))

    -- local scope to evaluate block
    local localvars_save = localvars
    localvars = newscope()
    localvars = localvars_save
    block_cast:append(C.lua_settop(C.Id(id)))
    block_cast:append(genblock(block_ast))
    cast:append(C.While(1, block_cast))
    append_array(cast.pre, block_cast.pre)
  end

  cast:append(C.lua_settop(C.Id(id)))
  return cast
end


-- Converts Lua `Do AST to C AST.
local function gendo(ast)
  local cast = cexpr()
  local id = nextid(); cast:append(C.Let(id, C.lua_gettop()))

  do
    -- local scope to evaluate block
    local localvars_save = localvars
    localvars = newscope()
    cast:append(genblock(ast))
    localvars = localvars_save
    cast:append(C.lua_settop(C.Id(id)))
  end

  cast:append(C.lua_settop(C.Id(id)))
  return cast
end


-- Converts Lua `Local AST to C AST.
local function genlocalstat(ast)
  local names_ast, vals_ast = ast[1], ast[2]
  local cast = cexpr()

  local id
  if #names_ast > #vals_ast then
    id = nextid(); cast:append(C.Let(id, C.lua_gettop()))
  end

  for i,val_ast in ipairs(vals_ast) do
    cast:append(genexpr(val_ast, 'onstack',
      #names_ast > #vals_ast and i == #vals_ast and 'multret'))
  end
  for i,name_ast in ipairs(names_ast) do
    local name = name_ast[1]; assert(name_ast.tag == 'Id')
    idxtop = idxtop + 1
    localvars[name] = idxtop
  end

  if #names_ast > #vals_ast then
    cast:append(C.lua_settop(C.Op('+', C.Id(id), #names_ast)))
  elseif #names_ast < #vals_ast then
    cast:append(C.lua_pop(#vals_ast - #names_ast))
  end
  return cast
end

local function genstatement(stat_ast)
  local cast
  if stat_ast.tag == 'Set' then
    -- note: supports x,y=y,x
    local l_ast, r_ast = stat_ast[1], stat_ast[2]
    cast = cexpr()
    for i=1,#r_ast do
      cast:append(genexpr(r_ast[i], 'onstack'))
    end
    for i=#r_ast,1,-1 do
      cast:append(genlvalueassign(l_ast[i]))
    end
  elseif stat_ast.tag == 'Return' then
    cast = cexpr()
    local can_multi = #stat_ast >= 1 and
      (stat_ast[#stat_ast].tag == 'Call' or
       stat_ast[#stat_ast].tag == 'Invoke')
    local id
    if can_multi then
      id = nextid(); cast:append(C.Let(id, C.lua_gettop()))
    end
    for i,e_ast in ipairs(stat_ast) do
      cast:append(genexpr(e_ast, 'onstack',
        i==#stat_ast and can_multi and 'multret' or 1))
    end
    if id then
      cast:append(C.Return(C.Op('-', C.lua_gettop(), C.Id(id))))
    else
      cast:append(C.Return(#stat_ast))
    end
  elseif stat_ast.tag == 'Fornum' then
    cast = genfornum(stat_ast)
  elseif stat_ast.tag == 'Forin' then
    cast = genforin(stat_ast)
  elseif stat_ast.tag == 'While' then
    cast = genwhile(stat_ast)
  elseif stat_ast.tag == 'Do' then
    cast = gendo(stat_ast)
  elseif stat_ast.tag == 'If' then
    cast = genif(stat_ast)
  elseif stat_ast.tag == 'Call' or stat_ast.tag == 'Invoke' then
    cast = genexpr(stat_ast, 'onstack', 0)
  elseif stat_ast.tag == 'Local' then
    cast = genlocalstat(stat_ast)
  elseif stat_ast.tag == 'Localrec' then
    assert(false, 'FIX: Localrec NOT IMPL')
  elseif stat_ast.tag == 'Break' then
    cast = cexpr(C.Break()) --FIX: if any cleanup on scope exit needed
  else
    assert(false, stat_ast.tag)
  end 

  assert(cast[1], table.tostring(cast))
  local comment = getlines(src, linerange(stat_ast))
  cast[1].comment = comment

  return cast
end

--local
function genblock(ast)
  local cast = cexpr()
  for _,stat_ast in ipairs(ast) do
    cast:append(genstatement(stat_ast))
  end
  return cast
end

local function gendefinitions(ast)
  local cast = C.Def()
  for _,def_ast in ipairs(ast) do
    cast:append(genstatement(def_ast))
  end
  return cast
end

local function genmainchunk(ast)
  local cast = cexpr()
  local cast_block = genblock(ast)
  cast_block:append(C.Return(0))
  append_array(cast, cast_block.pre)
  cast:append(C.Functiondef('luamain', cast_block))
  return cast
end

local function genfull(ast)

  local cast = cexpr(); cast.tag = 'Def'

  cast:append(C.C [[
/* WARNING: This file was automatically generated by lua2c. */

#ifdef __cplusplus
extern "C" {
#endif
#include <lua.h>
#include <lauxlib.h>
#include <lualib.h>
#ifdef __cplusplus
}
#endif
#include <stdio.h>
#include <stdlib.h>
]])

  cast:append(genmainchunk(ast))

  cast:append(C.C [[
/* from lua.c */
static int traceback (lua_State *L) {
  if (!lua_isstring(L, 1))  /* 'message' not a string? */
    return 1;  /* keep it intact */
  lua_getfield(L, LUA_GLOBALSINDEX, "debug");
  if (!lua_istable(L, -1)) {
    lua_pop(L, 1);
    return 1;
  }
  lua_getfield(L, -1, "traceback");
  if (!lua_isfunction(L, -1)) {
    lua_pop(L, 2);
    return 1;
  }
  lua_pushvalue(L, 1);  /* pass error message */
  lua_pushinteger(L, 2);  /* skip this function and traceback */
  lua_call(L, 2, 1);  /* call debug.traceback */
  return 1;
}
]])

  cast:append(C.C [[
typedef struct {
  int c;
  const char ** v;
} lc_args_t;
]])

  cast:append(C.C [[
/* create global arg table */
static void lc_createarg(lua_State * L, lc_args_t * args) {
  int i;
  lua_newtable(L);
  for (i=0; i < args->c; i++) {
    lua_pushstring(L, args->v[i]);
    lua_rawseti(L, -2, i);
  }
  lua_setglobal(L, "arg");
}
]])

  cast:append(C.C [[
static int lc_pmain(lua_State * L) {
  luaL_openlibs(L);

  lc_createarg(L, (lc_args_t*)lua_touserdata(L, 1));

  lua_pushcfunction(L, traceback);
  lua_pushcfunction(L, luamain);
  int status = lua_pcall(L, 0, 0, -2);
  if (status != 0) {
    fputs(lua_tostring(L,-1), stderr);
  }
  return 0;
}
]])

  cast:append(C.C [[
int main(int argc, const char ** argv) {
  lc_args_t args = {argc, argv};
  lua_State * L = luaL_newstate();
  if (! L) { fputs("Failed creating Lua state.", stderr); exit(1); }

  int status = lua_cpcall(L, lc_pmain, &args);
  if (status != 0) {
    fputs(lua_tostring(L,-1), stderr);
  }

  lua_close(L);
  return 0;
}
]])

  return cast
end


--
-- SECTION: Converts C AST to C code string.
--


-- Indents lines of code.
local function indentcode(code)
  local indent = '  '
  code = code:gsub('\n', '\n' .. indent)
  code = code:gsub(indent .. '$', '')
  if code ~= "" then code = indent .. code end
  return code
end


-- Makes C comment of string s.
local function ccomment(s)
  s = s:gsub('%*%/', '* /')
  s = '/* ' .. s:gsub('\n', '\n' .. ' * ') .. ' */'
  return s
end


-- Tests whether C AST node of given type should not have semicolon
-- appended.
local no_semicolon = {
  ['If'] = true,
  ['While'] = true,
  ['Functiondef'] = true,
  ['C'] = true
}

-- Converts C AST to C code string.
local function cast_tostring(cast)
  if type(cast) ~= 'table' then
    if type(cast) =='number' then  -- convenience function
      return tostring(cast)
    elseif type(cast) == 'string' then  -- convenience function
      return string.format("%q", cast):gsub('\\\n', '\\n')
    else
      assert(false, type(cast))
    end
  elseif cast.tag == 'C' or cast.tag == 'Id' then
    local ccode = cast[1]
    assert(type(ccode) == 'string')
    return ccode
  elseif cast.tag == 'Op' then
    local opid, a_cast, b_cast = cast[1], cast[2], cast[3]
    local pa,pz = '(', ')'  -- improve: sometimes can be avoided
    return pa .. cast_tostring(a_cast) ..
           ' ' .. opid .. ' ' .. cast_tostring(b_cast) .. pz
  elseif cast.tag == 'Let' then
    local id, val_cast = cast[1], cast[2]
    return "const int " .. id .. " = " .. cast_tostring(val_cast)
  elseif cast.tag == 'LetDouble' then
    local id, val_cast = cast[1], cast[2]
    return "const double " .. id .. " = " .. cast_tostring(val_cast)
  elseif cast.tag == 'LetMutableDouble' then
    local id, val_cast = cast[1], cast[2]
    return "double " .. id .. " = " .. cast_tostring(val_cast)
  elseif cast.tag == 'Not' then
    local a_ast = cast[1]
    local pa,pz = '(', ')'  -- improve: sometimes can be avoided
    return '!' .. pa .. cast_tostring(a_ast) .. pz
  elseif cast.tag == 'Return' then
    local a_ast = cast[1]
    return 'return' .. (a_ast and ' ' .. cast_tostring(a_ast) or '')
  elseif cast.tag == 'Break' then
    return 'break'
  elseif cast.tag == 'CallL' then
    local args = {tag='C', 'L'}
    for i=2,#cast do
      args[#args+1] = cast_tostring(cast[i])
    end
    return cast[1] .. '(' .. table.concat(args, ',') .. ')'
  elseif cast.tag == 'Def' then
    local ts = {}
    for i,stat_cast in ipairs(cast) do
      ts[i] = cast_tostring(stat_cast) .. '\n\n'
    end
    local ccode = table.concat(ts)
    return ccode
  elseif cast.tag == nil then -- block
    local ts = {}
    for i,stat_cast in ipairs(cast) do
      local comment = ''
      if stat_cast.comment then
        comment = '\n' .. ccomment(stat_cast.comment) .. '\n'
      end
      local semi = no_semicolon[stat_cast.tag] and '' or ';'
      ts[i] = comment .. cast_tostring(stat_cast) .. semi .. '\n'
    end
    local ccode = indentcode(table.concat(ts))
    return ccode
  elseif cast.tag == 'If' then
    local ccode = ''
    for i=2,#cast,2 do
      if i ~= 2 then ccode = ccode .. 'else ' end
      ccode = ccode .. 'if (' .. cast_tostring(cast[i-1]) .. ') {\n' ..
              cast_tostring(cast[i]) .. '}'
    end
    if #cast % 2 == 1 then
      ccode = ccode .. '\nelse {\n' .. cast_tostring(cast[#cast]) .. '}'
    end
    return ccode
  elseif cast.tag == 'While' then
    local expr_cast, block_cast = cast[1], cast[2]
    local ccode = 'while (' .. cast_tostring(expr_cast) .. ') {\n' ..
                  cast_tostring(block_cast) .. '}'
    return ccode
  elseif cast.tag == 'Functiondef' then
    local id, body_cast = cast[1], cast[2]
    local comment = ''
    if cast.comment then
      comment = ccomment(cast.comment) .. '\n'
    end
    local ccode =
      comment ..
      'static int ' .. id .. ' (lua_State * L) {\n' ..
      cast_tostring(body_cast) .. '}\n'
    return ccode
  elseif cast.tag:find'lua_' == 1 then  -- convenience function
    return cast_tostring{tag='CallL', cast.tag, unpack(cast)}
  else
    assert(false, cast.tag)
  end
end


--
-- SECTION: Driver.
--


local src_filename = ...

if not src_filename then
  io.stderr:write("usage: lua2c filename.lua\n")
  os.exit(1)
end

local src_file = io.open (src_filename, 'r')
src            = src_file:read '*a'; src_file:close()
local ast      = mlc.ast_of_luastring (src)

-- io.stderr:write(table.tostring(ast, "nohash", 60))

local cast = genfull(ast)

-- io.stderr:write(table.tostring(cast, "nohash", 60))

io.stdout:write(cast_tostring(cast))



