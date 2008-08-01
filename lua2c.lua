-- lua2c - convert Lua 5.1 source to C code.
--
-- STATUS:
--   WARNING: This code passes much of the Lua 5.1 test suite,
--   but the code is new and there can still be errors.  In particular,
--   a few language features (e.g. coroutines) are not implemented.
--
--   Unimplemented Lua language features:
--    - deprecated old style vararg (arg) table inside vararg functions
--      (LUA_COMPAT_VARARG)
--    - debug.getinfo(f, 'n').name for C-based functions
--    - setfenv does not permit C-based functions
--    - how well do tail call optimizations work?
--    - how to handle coroutines? (see README)
--    Note: A few things (coroutines) might remain
--      unimplemented--see README file file for details.
--
--   Possible improvements:
--    - Fix: large numerical literals can give gcc warnings such as
--      'warning: integer constant is too large for "long" type').
--      Literal numbers are rendered as C integers literals (e.g. 123)
--      rather than C double literals (eg. 123.0).  
--    - Generated C functions could be named based on the Lua function
--      name.
--    - improved debug tracebacks on exceptions
--    - See items marked FIX in below code.
--
-- SOURCE:
--
--   http://lua-users.org/wiki/LuaToCee
--   (c) 2008 David Manura.  Licensed in the same terms as Lua (MIT license).
--   See included LICENSE file for full licensing details.
--   Please post any patches/improvements.
--

package.path = package.path .. ';./lib/?.lua'


-- gg/mlp Lua parsing Libraries taken from Metalua.
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

-- LUA_MINSTACK value in luaconf.h
local LUA_MINSTACK = 20

--
-- SECTION: Utility
--


local function NOTIMPL(s)
  error('FIX - NOT IMPLEMENTED: ' .. s, 2)
end

local function DEBUG(...)
  local ts = {...}
  for i,v in ipairs(ts) do
    ts[i] = table.tostring(v,'nohash',60)
  end
  io.stderr:write(table.concat(ts, ' ') .. '\n')
end

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


-- info on current scope. includes
-- table of local variables.
-- Maps name -> stack index
local currentscope = {['.closurelevel'] = 0}

-- Information on function currently being compiled.
local funcinfo = {is_vararg=false, nformalparams=0,
  is_lc_nextra_used=false, is_lc_nactualargs_used=false,
  is_lc_nextra_used_debug=false, is_lc_nactualargs_used_debug=false,
  idxtopmax = 0
  --old: outervars={}
}


-- topmost stack index
local idxtop = 0

-- Mutators for idxtop.
local function idxtop_change(n)
  idxtop = idxtop + n
  funcinfo.idxtopmax = math.max(funcinfo.idxtopmax, idxtop)
end
local function idxtop_pad(n)
  
end
local function idxtop_restore(idx)
  assert(idx <= idxtop)
  idxtop = idx
end

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
-- Only for binary arthmetic ops.
local opid_to_c = {
  ["add"]=function(a,b) return a .. ' + ' .. b end,
  ["sub"]=function(a,b) return a .. ' - ' .. b end,
  ["mul"]=function(a,b) return a .. ' * ' .. b end,
  ["div"]=function(a,b) return a .. ' / ' .. b end,
  ["mod"]=function(a,b) return
            a .. ' - floor(' .. a .. '/' .. b ..')*' .. b end,
          -- caution: a and b evaluate twice
          -- note: requies math.h
  ["pow"]=function(a,b) return 'pow(' .. a .. ',' .. b .. ')' end,
          -- note: requies math.h
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
    assert(false, tostring(obj))
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
  return cast2  --FIX:improve style?
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

local function tag(o)
  return type(o) == 'table' and o.tag or nil
end

-- Adjusts absolute index of local variable,
-- given that in vararg (...) functions, base index depends on
-- arguments passed in.  Can return C AST.
local function realidx(idx)
  -- pseudoindex
  if type(idx) == 'table' and idx.tag == 'C' and
     idx[1] == 'lua_upvalueindex(1)'
  then
    return idx
  end
  local idxreal = tag(idx) == 'Upval' and idx[1] or idx
  if funcinfo.is_vararg and
     (tag(idxreal) == 'Id' or idxreal > funcinfo.nformalparams)
  then
    if tag(idx) == 'Upval' then
      -- no adjustment
    else
      idx = C.Op('+', idx, C.Id'lc_nextra')
      funcinfo.is_lc_nextra_used = true
    end
  end
  return idx  
end

-- Gets real index of local var.
local function localidx(name)
  local idx = currentscope[name]
  if not idx then return end

  return realidx(idx)
end


--old: local function isupvalue(name)
--  return not currentscope[name] and funcinfo.outervars[name]
--end

-- Adjusts stack index to relative (negative) position offset.  note:
-- use only when values inside offset are on the stack
-- (non-psuedoindices).
-- Note: allows C AST.
local function adjustidx(offset, idx)
  if type(idx) == 'table' or idx > 0 then
    return idx
  else -- relative stack index or pseudoindex
     -- FIX:pseudoindices not supported?
    return idx + offset + 1
  end
end

-- Adjusts relative stack indicies
-- Note: allows C ASTs.
local function adjustidxs(...)
  local nused = 0
  local result = {...}
  for i=#result,1,-1 do
    local idx = result[i]
    if type(idx) ~= 'table' and idx < 0 then
            --FIX: and idx > LUA_REGISTRYINDEX ?
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


-- Gets range of line/column numbers (line1, line2)
-- represented by AST.
-- Returns nothing if not information found.
-- IMPROVE:hack.  Does gg/mlp already provide this?
--   Could this support character positions too?
local function linerange(ast)
  if ast.lineinfo then
    return ast.lineinfo.first, ast.lineinfo.last
  end
  local line1, line2
  for i,ast2 in ipairs(ast) do
    if type(ast2) == 'table' then
      local line1_, line2_ = linerange(ast2)
      if line1_ and (not line1 or line1_ < line1) then
        line1 = line1_
      end
      if line2_ and (not line2 or line2_ > line2) then
        line2 = line2_
      end
    end
  end
  if line1 then
    return line1, line2
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


-- Appends comment to C AST node.
local function addcomment(cast, comment)
  local s = cast.comment and cast.comment .. '\n' .. comment or comment
  cast.comment = s
end

-- Prepends comment to C AST node.
local function prependcomment(cast, comment)
  local s = cast.comment and comment .. '\n' .. cast.comment or comment
  cast.comment = s
end

-- Gets next unique ID.  Useful in variable names to
-- ensure uniqueness.
local _id = 0
local function nextid()
  _id = _id + 1
  return 'lc' .. _id
end

-- Gets next unique ID for lexical variable.
local _varid = 0
local function nextvarid()
  _varid = _varid + 1
  return _varid
end

local function newscope()
  local currentscope_old = currentscope
  currentscope = setmetatable({}, {__index = currentscope_old})
  return currentscope_old
end

local function restorescope(currentscope_save)
  currentscope = currentscope_save
end

local function restorestackrel(cast, idx_old)
  local npushed = idxtop - idx_old
  if npushed ~= 0 then
    cast:append(C.lua_pop(npushed))
    addcomment(cast[#cast], 'internal: stack cleanup on scope exit')
  end
  idxtop_change(- npushed)
end

local function restorestackabs(cast, idx_old_cast, idx_old)
  cast:append(C.lua_settop(realidx(idx_old_cast)))
  idxtop_restore(idx_old)
end


-- Returns whether expression could possibly return a number of argument
-- different from 1.
-- note: expr_ast can be nil
local function can_multi(expr_ast)
  return expr_ast and (expr_ast.tag == 'Call' or expr_ast.tag == 'Invoke'
                       or expr_ast.tag == 'Dots')
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


local function get_closuretableidx_cast()
  return localidx('.closuretable')
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
static void lc_%s(lua_State * L, int idxa, int idxb) {
  if (lua_isnumber(L,idxa) && lua_isnumber(L,idxb)) {
    lua_pushnumber(L,%s);
  }
  else {
    if (luaL_getmetafield(L,idxa,"__%s")||luaL_getmetafield(L,idxb,"__%s")) {
      lua_pushvalue(L,idxa < 0 && idxa > LUA_REGISTRYINDEX ? idxa-1 : idxa);
      lua_pushvalue(L,idxb < 0 && idxb > LUA_REGISTRYINDEX ? idxb-2 : idxb);
      lua_call(L,2,1);
    }
    else {
      luaL_error(L, "attempt to perform arithmetic");
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

  if opid == 'pow' or opid == 'mod' then
    if not is_created['math.h'] then
      append_array(cast.pre, {C.Include'<math.h>'})
      is_created['math.h'] = true
    end
  end

  local fname = "lc_" .. opid
  if not is_created[fname] then
    append_array(cast.pre, {makebinop(opid)})
    is_created[fname] = true
  end

  local a_idx = cast:append(genexpr(a_ast, 'anywhere')).idx
  local b_idx = cast:append(genexpr(b_ast, 'anywhere')).idx
  local nstack = countstack(a_idx, b_idx)
  a_idx, b_idx = adjustidxs(a_idx, b_idx)
  cast:append(C.CallL('lc_'..opid, a_idx, b_idx))
  for i=1,nstack do
    cast:append(C.lua_remove(-2))
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


local function genlenop(ast, where)
  local opid, a_ast = ast[1], ast[2]

  local cast = cexpr()
  local a_idx = cast:append(genexpr(a_ast, 'anywhere')).idx

  --FIX:call metatable __len for userdata?
  local id = nextid()
  cast:append(C.LetDouble(id, C.lua_objlen(a_idx)))
  if a_idx == -1 then
    cast:append(C.lua_pop(1))
  end
  cast:append(C.lua_pushnumber(C.Id(id)))
  return cast
end



local function genunmop(ast, where)
  -- Returns C AST node definition of op.
  local function makeop()
    local ccode = [[
/* __unm metamethod handler.
 * warning: assumes indices in range LUA_REGISTRYINDEX < x < 0 are relative. */
static void lc_unm(lua_State * L, int idxa) {
  if (lua_isnumber(L,idxa)) {
    lua_pushnumber(L,- lua_tonumber(L, idxa));
  }
  else {
    if (luaL_getmetafield(L,idxa,"__unm")) {
      lua_pushvalue(L,idxa < 0 && idxa > LUA_REGISTRYINDEX ? idxa-1 : idxa);
      lua_call(L,1,1);
    }
    else {
      luaL_error(L, "attempt to perform arithmetic");
    }
  }
}
]]
    return C.C(ccode)
  end

  local opid, a_ast = ast[1], ast[2]
  assert(opid == 'unm')

  local cast = cexpr()

  local fname = "lc_" .. opid
  if not is_created[fname] then
    append_array(cast.pre, {makeop()})
    is_created[fname] = true
  end

  local a_idx = cast:append(genexpr(a_ast, 'anywhere')).idx
  local nstack = countstack(a_idx)
  a_idx = adjustidxs(a_idx)
  cast:append(C.CallL('lc_'..opid, a_idx))
  for i=1,nstack do
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

-- note: call activate_closure_table() afterward.
local function gennewclosuretable(cast)
  local cast = cexpr()

  if not is_created['lc_newclosuretable'] then
    -- note: index idx cannot be relative.
    -- note: key 0 points to parent table.
    local body_cast = cexpr()
    --IMPROVE: C.C usage
    body_cast:append(C.C[[
/* pushes new closure table onto the stack, using closure table at
 * given index as its parent */
static void lc_newclosuretable(lua_State * L, int idx) {]])

    body_cast:append( cexpr( cexpr(
      C.lua_newtable(),
      C.lua_pushvalue(C.Id'idx'),
      C.lua_rawseti(-2,0)
    )))
    body_cast:append(C.C'}')

    append_array(cast.pre, body_cast)

    is_created['lc_newclosuretable'] = true
  end

  cast:append(C.CallL('lc_newclosuretable', get_closuretableidx_cast()))
  idxtop_change(1)

  local id = nextid()
  cast:append(C.Enum(id, idxtop))
  if not is_created['assert.h'] then
    append_array(cast.pre, {C.Include'<assert.h>'})
    is_created['assert.h'] = true
  end
  cast:append(C.Call('assert', C.Op('==', C.lua_gettop(), realidx(C.Id(id)))))

  cast.idx = C.Id(id)

  return cast
end

local function activate_closure_table(idx)
  currentscope['.closuretable'] = idx
  currentscope['.closurelevel'] = currentscope['.closurelevel'] + 1
end

-- helper function to generate function definition
local function genfunctiondef(ast, ismain)
  local params_ast, body_ast = ast[1], ast[2]

  -- localize new function info.
  local funcinfo_old = funcinfo
  local has_vararg = params_ast[#params_ast]
                     and params_ast[#params_ast].tag == 'Dots'
  local nformalargs = #params_ast - (has_vararg and 1 or 0)
  funcinfo = {is_vararg = has_vararg, nformalparams = nformalargs,
    is_lc_nextra_used = false, is_lc_nactualargs_used=false,
    is_lc_nextra_used_debug = false, is_lc_nactualargs_used_debug=false,
    idxtopmax = 0
    --old: outervars = currentscope
  }

  -- note: special usage of idxtop
  local idxtop_old = idxtop
  idxtop = 0

  -- localize code
  local currentscope_save = newscope()
  currentscope['.closuretable'] = C.C'lua_upvalueindex(1)'

  -- define parameters as local variables.
  for i,var_ast in ipairs(params_ast) do
    if var_ast.tag ~= 'Dots' then
      assert(var_ast.tag == 'Id')
      local varname = var_ast[1]
      currentscope[varname] = i
      idxtop_change(1)
    end
  end

  local body_cast = cexpr()

  local is_upvalue = false
  for i,params_ast in ipairs(params_ast) do
    is_upvalue = is_upvalue or params_ast.upvalue
  end
  if is_upvalue then
    local ct_idx = body_cast:append(gennewclosuretable()).idx
    activate_closure_table(ct_idx)

    for i=1,nformalargs do
      local param_ast = params_ast[i]

      if param_ast.upvalue then
        local name = param_ast[1]
        local varid = nextvarid()

        -- create local symbol
        currentscope[name] =
          {tag='Upval', idxtop, currentscope['.closurelevel'], varid}

        body_cast:append(C.lua_pushvalue(i))
        body_cast:append(C.lua_rawseti(-2, varid))
      end
    end
  end

  -- generate body
  body_cast:append(genblock(body_ast))

  local bodypre_cast = cexpr()

  -- Ensure stack space.
  local fudge = 10 -- allow some extra space, avoiding detailed
                   -- accounting. FIX: is this always sufficient?
  if funcinfo.idxtopmax + fudge >= LUA_MINSTACK then
    bodypre_cast:append(C.lua_checkstack(funcinfo.idxtopmax + fudge))
  end

  -- note: do after generating body do that funcinfo params are set
  -- note: safety in case caller passes more or less arguments
  -- than parameters.  IMPROVE-some of this is sometimes not necessary.
  bodypre_cast:append(C.Enum('lc_nformalargs', nformalargs))
  if #params_ast > 0 and params_ast[#params_ast].tag == 'Dots' or
     ismain  -- dots implicit in main chunk
  then
    if nformalargs > 0 then
      bodypre_cast:append(
        C.If(C.Op('<', C.lua_gettop(), C.Id'lc_nformalargs'),
          { C.lua_settop(C.Id'lc_nformalargs') } ))
    end
    -- note: measure nactualargs after adjustment above
    -- (important for genexpr of `Id)
    if funcinfo.is_lc_nextra_used then
      funcinfo.is_lc_nactualargs_used = true
    elseif funcinfo.is_lc_nextra_used_debug then
      funcinfo.is_lc_nactualargs_used_debug = true
    end

    if funcinfo.is_lc_nactualargs_used then
      bodypre_cast:append(C.LetInt('lc_nactualargs', C.lua_gettop()))
    elseif funcinfo.is_lc_nactualargs_used_debug then
      bodypre_cast:append(C.C'#ifndef NDEBUG')
      bodypre_cast:append(C.LetInt('lc_nactualargs', C.lua_gettop()))
      bodypre_cast:append(C.C'#endif')
    end
    if funcinfo.is_lc_nextra_used then
      bodypre_cast:append(C.LetInt('lc_nextra',
        C.Op('-', C.Id'lc_nactualargs', C.Id'lc_nformalargs')))
    elseif funcinfo.is_lc_nextra_used_debug then
      bodypre_cast:append(C.C'#ifndef NDEBUG')
      bodypre_cast:append(C.LetInt('lc_nextra',
        C.Op('-', C.Id'lc_nactualargs', C.Id'lc_nformalargs')))
      bodypre_cast:append(C.C'#endif')
    end
  else
    bodypre_cast:append(C.lua_settop(#params_ast))
  end

  -- prepend bodypre_cast to body_cast (IMPROVE: add prepend method?)
  local body_old_cast = body_cast
  local body_cast = cexpr()
  body_cast:append(bodypre_cast)
  body_cast:append(body_old_cast)

  if #body_ast == 0 or body_ast[#body_ast].tag ~= 'Return' then
    body_cast:append(C.Return(0))
  end

  local id = ast.is_main and 'lc_main'
             or nextid() .. '_func'  -- IMPROVE: deduce function name
  local def_cast = cexpr()
  append_array(def_cast, body_cast.pre)
  local func_cast = C.Functiondef(id, body_cast)
  func_cast.comment = getlines(src, linerange(ast))
  func_cast.id = id
  append_array(def_cast, { func_cast })

  restorescope(currentscope_save)
  idxtop = idxtop_old

  funcinfo = funcinfo_old

  return def_cast
end


local function genfunction(ast, where)
  local cast = cexpr()

  --## generate function definition
  local def_cast = genfunctiondef(ast)
  append_array(cast.pre, def_cast)

  --## generate function object
  if ast.uses_upvalue then
    cast:append(C.lua_pushvalue(get_closuretableidx_cast()))
    cast:append(C.lua_pushcclosure(C.Id(def_cast[#def_cast].id), 1))
  else
    cast:append(C.lua_pushcfunction(C.Id(def_cast[#def_cast].id)))
  end

  return cast
end


local function genmainchunk(ast)
  local astnew = {tag='Function', is_main=true, {{tag='Dots'}}, ast}

  return genfunctiondef(astnew, true)
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
  for i,e_ast in ipairs(ast) do
    if e_ast.tag == 'Pair' then
      local k_ast, v_ast = e_ast[1], e_ast[2]
      cast:append(genexpr(k_ast, 'onstack'))
      cast:append(genexpr(v_ast, 'onstack'))
      cast:append(C.lua_rawset(-3))
    else
      local can_multret = i == #ast and can_multi(e_ast)

      if can_multret then
        -- table marker
        local id = nextid()
        cast:append(C.Let(id, C.lua_gettop()))

        -- get list of values
        cast:append(genexpr(e_ast, 'onstack', 'multret'))

        -- push list of values in table.
        -- note: Lua spec does not prohibit right-to-left insertion.
        -- IMPROVE? right-to-left insertion can cause needless placement
        -- of values into the hash part of the table.
        cast:append(
          C.While(C.Op('>', C.lua_gettop(), C.Id(id)), {
            C.lua_rawseti(C.Id(id),
              C.Op('+', pos, C.Op('-', C.lua_gettop(), C.Id(id)))) } ))
      else
        cast:append(genexpr(e_ast, 'onstack'))
        pos = pos + 1
        cast:append(C.lua_rawseti(-2, pos))
      end
    end
  end
  return cast
end

local function gencall(ast, where, nret)
  local isinvoke = ast.tag == 'Invoke'  -- method call

  local cast = cexpr()

  -- whether last argument might possibly return multiple values
  local can_multret = can_multi(ast[#ast])

  -- push function
  if isinvoke then
    local obj_ast = ast[1]
    cast:append(genexpr(obj_ast, 'onstack')) -- actually self
  else
    assert(ast.tag == 'Call')
    local f_ast = ast[1]
    cast:append(genexpr(f_ast, 'onstack'))
  end

  -- argument marker
  local id
  if can_multret then
    id = nextid(); cast:append(C.Let(id, C.lua_gettop()))
  end

  -- push arguments
  for i=2,#ast do
    if i == 2 and isinvoke then
      local methodname_ast = ast[i]
      cast:append(genexpr(methodname_ast, 'onstack'))
      cast:append(C.lua_gettable(-2))
      cast:append(C.lua_insert(-2))  -- swap self and function
    else
      cast:append(genexpr(ast[i], 'onstack', i == #ast and 'multret' or false))
    end
  end
  local narg = can_multret and C.Op('-', C.lua_gettop(), C.Id(id)) or #ast-1

  -- call
  cast:append(C.lua_call(narg,
    nret == 'multret' and C.C'LUA_MULTRET' or nret or 1))

  return cast
end


-- helper
local function gen_lc_setupvalue(...)
  local cast = cexpr(C.CallL('lc_setupvalue', ...))
  if not is_created['lc_setupvalue'] then
    append_array(cast.pre, {C.C[[
static void lc_setupvalue(lua_State * L, int tidx, int level, int varid) {
  if (level == 0) {
    lua_rawseti(L,tidx,varid);
  }
  else {
    lua_pushvalue(L,tidx);
    while(--level >= 0) {
      lua_rawgeti(L,tidx,0); /* 0 links to parent table */
      lua_remove(L,-2);
      tidx = -1;
    }
    lua_insert(L,-2);
    lua_rawseti(L,-2,varid);
    lua_pop(L,1);
  }
}
]]})
    is_created['lc_setupvalue'] = true
  end
  return cast
end

-- helper
local function gen_lc_getupvalue(tidx, level, varid)
  assert(tidx and level and varid)
  local cast = cexpr(C.CallL('lc_getupvalue', tidx, level, varid))
  if not is_created['lc_getupvalue'] then
    append_array(cast.pre, {C.C[[
/* gets upvalue with ID varid by consulting upvalue table at index
 * tidx for the upvalue table at given nesting level. */
static void lc_getupvalue(lua_State * L, int tidx, int level, int varid) {
  if (level == 0) {
    lua_rawgeti(L,tidx,varid);
  }
  else {
    lua_pushvalue(L,tidx);
    while (--level >= 0) {
      lua_rawgeti(L,tidx,0); /* 0 links to parent table */
      lua_remove(L,-2);
      tidx = -1;
    }
    lua_rawgeti(L,-1,varid);
    lua_remove(L,-2);
  }
}
]]})
    is_created['lc_getupvalue'] = true
  end
  return cast
end

local function gennumber(x, pre_cast)
  if x == math.huge or x == -math.huge then
    if not is_created['math.h'] then
      append_array(pre_cast, {C.Include'<math.h>'})
      is_created['math.h'] = true
    end
  end
  return x
end

-- local
function genexpr(ast, where, nret)
  if ast.tag == 'Op' then
    ast = constant_fold(ast)
  end

  if ast.tag == 'Nil' then
    return cexpr(C.lua_pushnil())
  elseif ast.tag == 'Dots' then
    if nret == 'multret' then
      funcinfo.is_lc_nactualargs_used = true
      return cexpr(C.C[[{int i; for (i=lc_nformalargs+1; i<=lc_nactualargs; i++) { lua_pushvalue(L, i); }}]])
    elseif nret and nret > 1 then
      funcinfo.is_lc_nextra_used = true
      return cexpr(C.C([[
/* ... */
{ int i;
  const int idx = lua_gettop(L);
  const int npush = (]] .. nret .. [[ <= lc_nextra) ? ]] .. nret .. [[ : lc_nextra;
  for (i=lc_nformalargs+1; i<=lc_nformalargs+npush; i++) { lua_pushvalue(L, i); }
  lua_settop(L, idx + ]] .. nret .. [[); }]]))
    else
      return cexpr(C.lua_pushvalue(C.Op('+', C.Id'lc_nformalargs', 1)));
    end
  elseif ast.tag == 'True' then
    return cexpr(C.lua_pushboolean(1))
  elseif ast.tag == 'False' then
    return cexpr(C.lua_pushboolean(0))
  elseif ast.tag == 'Number' then
    local cast = cexpr()
    cast:append(C.lua_pushnumber(gennumber(ast[1], cast.pre)))
    return cast
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
        assert(false, opid)
      end
    elseif is_unopid[opid] then
      if opid == 'not' then
        return gennotop(ast, where)
      elseif opid == 'len' then
        return genlenop(ast, where)
      elseif opid == 'unm' then
        return genunmop(ast, where)
      else
        assert(false, opid)
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
    if currentscope[name] then -- local
      local idx = localidx(name)
      if tag(idx) == 'Upval' then
        local closuretable_idx, closurelevel, varid = idx[1], idx[2], idx[3]
        cast:append(gen_lc_getupvalue(
          get_closuretableidx_cast(),
          currentscope['.closurelevel'] - closurelevel, varid))
      elseif where == 'anywhere' then
        cast.idx = idx
        return cast
      else
        cast:append(C.lua_pushvalue(idx))
      end
    else -- global
      --old: cast:append(C.lua_getglobal(name))
      cast:append(C.lua_getfield(C.C'LUA_ENVIRONINDEX', name))
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
    if currentscope[name] then
      local idx = localidx(name)
      if tag(idx) == 'Upval' then
        local closuretable_idx, closurelevel, varid = idx[1], idx[2], idx[3]
        cast:append(gen_lc_setupvalue(
          get_closuretableidx_cast(),
          currentscope['.closurelevel'] - closurelevel, varid))
      else
        cast:append(C.lua_replace(idx))
      end
    else  -- global
      --old:cast:append(C.lua_setglobal(name))
      cast:append(C.lua_setfield(C.C'LUA_ENVIRONINDEX', name))
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

  local currentscope_save = currentscope

  local base_idx = idxtop
  local base_id = nextid()
  cast:append(C.Enum(base_id, base_idx))

  do
    local expr_ast, body_ast = ast[1], ast[2]

    idxtop_restore(base_idx)

    -- expression
    local a_idx = cast:append(genexpr(expr_ast, 'anywhere')).idx
    if a_idx ~= -1 then
      if_args[#if_args+1] = C.lua_toboolean(a_idx)
    else
      local id = nextid();
      cast:append(C.Let(id, C.lua_toboolean(-1)))
      cast:append(C.lua_pop(1))
      if_args[#if_args+1] = C.Id(id)
    end

    -- block
    newscope()
    local block_cast = genblock(body_ast)
    table.insert(if_args, block_cast)
    append_array(cast.pre, block_cast.pre)
    restorescope(currentscope_save)
  end

  if ast[3] then
    idxtop_restore(base_idx)

    local currentscope_save = newscope()
    local block_cast
    if not ast[4] then
      block_cast = genblock(ast[3])
    else
      local nested_ast = {tag='If'}
      for i=3,#ast do nested_ast[#nested_ast+1] = ast[i] end
      block_cast = genif(nested_ast)
    end
    table.insert(if_args, block_cast)
    append_array(cast.pre, block_cast.pre)
    restorescope(currentscope_save)
  end
  -- note: idx is (in general) indeterminant now
  -- due to the multiple branches.

  cast:append(C.If(unpack(if_args)))

  cast:append(C.lua_settop(realidx(C.Id(base_id))))
  idxtop_restore(base_idx)

  return cast
end


-- Converts Lua `Fornum AST to C AST.
local function genfornum(ast)
  local name_ast, e1_ast, e2_ast, e3_ast, block_ast =
    ast[1], ast[2], ast[3], ast[5] and ast[4] or ast[5], ast[5] or ast[4]
  local name_id = name_ast[1]; assert(name_ast.tag == 'Id')
  local cast = cexpr()

  local var_id = nextid() .. '_var';
  local limit_id = nextid() .. '_limit';
  local step_id = nextid() .. '_step';
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
  local currentscope_save = newscope()

  local block_cast = cexpr()

  local base_idx = idxtop
  local base_id = nextid()
  cast:append(C.Enum(base_id, base_idx))

  -- create local
  if name_ast.upvalue then
    local ct_idx = block_cast:append(gennewclosuretable()).idx
    activate_closure_table(ct_idx)

    local varid = nextvarid()
    block_cast:append(C.lua_pushnumber(C.Id(var_id)))
    block_cast:append(C.lua_rawseti(-2, varid))
    currentscope[name_id] =
      {tag='Upval', ct_idx, currentscope['.closurelevel'], varid}
  else
    block_cast:append(C.lua_pushnumber(C.Id(var_id)))
    idxtop_change(1)
    currentscope[name_id] = idxtop
  end
  block_cast[1].comment =
    string.format("internal: local %s at index %d", name_id, idxtop)

  block_cast:append(genblock(block_ast))

  restorestackrel(block_cast, base_idx)
  restorescope(currentscope_save)

  block_cast:append(C.C(var_id .. ' += ' .. step_id .. ';')) --IMPROVE?

  cast:append(C.While(while_expr_cast, block_cast))
  append_array(cast.pre, block_cast.pre)

  -- note: mixed breaks and locals can leave the stack at an
  -- unknown size, so absolute adjust here.
  restorestackabs(cast, C.Id(base_id), base_idx)

  return cast
end

-- Converts Lua `Forin AST to C AST.
local function genforin(ast)
  local names_ast, exprs_ast, block_ast = ast[1], ast[2], ast[3]
  local cast = cexpr()

  local multi = can_multi(exprs_ast[1])

  local base_idx = idxtop
  local base_id = nextid()
  cast:append(C.Enum(base_id, base_idx))

  -- loop invisible variables: var, limit, step
  local nlast = multi and 3 + 1 - #exprs_ast or 1
  for i,expr_ast in ipairs(exprs_ast) do
    cast:append(genexpr(expr_ast, 'onstack',
      i==#exprs_ast and math.max(0,nlast)))
  end
  if nlast < 0 then
    cast:append(C.lua_pop(-nlast))
  end
  idxtop_change(3)
  addcomment(cast[1], 'internal: local f, s, var = explist')

  local base2_idx = idxtop

  local block_cast = cexpr(); do

    -- local scope to evaluate block
    local currentscope_save = newscope()
    local extra = 0
    local ct_idx

    local is_upvalue = false
    for i,name_ast in ipairs(names_ast) do
      if name_ast.upvalue then is_upvalue = true end
    end
    if is_upvalue then
      ct_idx = block_cast:append(gennewclosuretable()).idx
      activate_closure_table(ct_idx)
      extra = 1
    end

    -- loop variables and control
    block_cast:append(C.lua_pushvalue(-3 - extra))
    addcomment(block_cast[#block_cast],
      'internal: local var_1, ..., var_n = f(s, var)\n' ..
      '          if var_1 == nil then break end\n' ..
      '          var = var_1')
    block_cast:append(C.lua_pushvalue(-3 - extra))
    block_cast:append(C.lua_pushvalue(-3 - extra))
    block_cast:append(C.lua_call(2,#names_ast))
    idxtop_change(#names_ast)
    block_cast:append(C.If(C.lua_isnil(- #names_ast), {C.Break()}))
    block_cast:append(C.lua_pushvalue(- #names_ast))
    block_cast:append(C.lua_replace(- #names_ast - 2 - extra))
    -- loop variables
    local pos1 = #block_cast
    local idx1 = idxtop - #names_ast
    do -- locals used as upvalues
      local varids = {}
      local nlocals = 0  -- number of non-up-value-enabled locals found
      for i=#names_ast,1,-1 do
        local name_ast = names_ast[i]
        if name_ast.upvalue then
          local name_id = name_ast[1]; assert(name_ast.tag == 'Id')
          varids[i] = nextvarid()
          if nlocals == 0 then
            block_cast:append(C.lua_rawseti(-1 - i, varids[i]))
          else
            block_cast:append(C.lua_pushvalue(-1 - nlocals))
            block_cast:append(C.lua_rawseti(realidx(ct_idx), varids[i])) 
            block_cast:append(C.lua_remove(-1 - nlocals))
          end
          idxtop_change(- 1)
          currentscope[name_id] =
            {tag='Upval', ct_idx, currentscope['.closurelevel'], varids[i]}
        else
          nlocals = nlocals + 1
        end
      end
      for i,name_ast in ipairs(names_ast) do if varids[i] then
        addcomment(block_cast[pos1+1],
          string.format("internal: upvalue-enabled local %s with id %d",
                        name_ast[1], varids[i]))
      end end
    end
    if pos1 == #block_cast then
      -- hack: ensure AST node exists in which to place comment.
      block_cast:append(C.C'')
    end
    do -- locals
      local count = 0
      for i,name_ast in ipairs(names_ast) do
        if not name_ast.upvalue then
          local name_id = name_ast[1]; assert(name_ast.tag == 'Id')
          count = count + 1
          currentscope[name_id] = idx1 + count
          addcomment(block_cast[pos1+1],
            string.format("internal: local %s with idx %d",
                          name_id, currentscope[name_id]))
        end
      end
    end

    -- block
    block_cast:append(genblock(block_ast))

    -- end scope
    restorestackrel(block_cast, base2_idx)
    restorescope(currentscope_save)
  end
  cast:append(C.While(1, block_cast))
  append_array(cast.pre, block_cast.pre)

  restorestackabs(cast, C.Id(base_id), base_idx)

  return cast
end


-- Converts Lua `While AST to C AST.
local function genwhile(ast)
  local expr_ast, block_ast = ast[1], ast[2]
  local cast = cexpr()

  local base_idx = idxtop
  local base_id = nextid()
  cast:append(C.Enum(base_id, base_idx))

  do
    -- expression
    local block_cast = cexpr(); do
      local expr_idx = block_cast:append(genexpr(expr_ast, 'anywhere')).idx
      block_cast:append(
        C.If(C.Not(C.lua_toboolean(expr_idx)), {C.Break()}))
      if expr_idx == -1 then
        block_cast:append(C.lua_pop(1))
      end

      -- local scope to evaluate block
      local currentscope_save = newscope()

      -- block
      block_cast:append(genblock(block_ast))

      restorestackrel(block_cast, base_idx)
      restorescope(currentscope_save)
    end

    cast:append(C.While(1, block_cast))
    append_array(cast.pre, block_cast.pre)
  end

  -- note: mixed breaks and locals can leave the stack at an
  -- unknown size, so absolute adjust here.
  restorestackabs(cast, C.Id(base_id), base_idx)

  return cast
end


-- Converts Lua `Repeat AST to C AST.
local function genrepeat(ast)
  local block_ast, expr_ast = ast[1], ast[2]
  local cast = cexpr()

  local base_idx = idxtop
  local base_id = nextid()
  cast:append(C.Enum(base_id, base_idx))

  do
    -- body
    local block_cast = cexpr(); do
      -- local scope to evaluate block and expression
      local currentscope_save = newscope()

      -- block
      block_cast:append(genblock(block_ast))

      -- expression
      local expr_idx = block_cast:append(genexpr(expr_ast, 'anywhere')).idx
      idxtop_change(1)
      block_cast:append(
        C.If(C.lua_toboolean(expr_idx), {C.Break()}))

      restorestackrel(block_cast, base_idx)
      restorescope(currentscope_save)
    end
    cast:append(C.While(1, block_cast))
    append_array(cast.pre, block_cast.pre)
  end

  -- note: mixed breaks and locals can leave the stack at an
  -- unknown size, so absolute adjust here.
  restorestackabs(cast, C.Id(base_id), base_idx)

  return cast
end


-- Converts Lua `Do AST to C AST.
local function gendo(ast)
  local cast = cexpr()

  local base_idx = idxtop

  -- local scope to evaluate block
  local currentscope_save = newscope()
  cast:append(genblock(ast))
  restorescope(currentscope_save)
  restorestackrel(cast, base_idx)

  return cast
end


-- Converts Lua `Local AST to C AST.
local function genlocalstat(ast)
  local names_ast, vals_ast = ast[1], ast[2]
  local cast = cexpr()

  local ct_idx
  local is_upvalue = false
  for i,name_ast in ipairs(names_ast) do
    is_upvalue = is_upvalue or name_ast.upvalue
  end
  if is_upvalue then
    ct_idx = cast:append(gennewclosuretable()).idx
  end

  -- create values
  for i,val_ast in ipairs(vals_ast) do
    cast:append(genexpr(val_ast, 'onstack',
      #names_ast > #vals_ast and i == #vals_ast and can_multi(val_ast) and
      (#names_ast - #vals_ast + 1)))
  end

  -- cleanup if LHS and RHS lengths don't match
  if #names_ast > #vals_ast and not can_multi(vals_ast[#vals_ast]) then
    cast:append(
      C.lua_settop(
        C.Op('+', C.lua_gettop(), #names_ast - #vals_ast)))
  elseif #names_ast < #vals_ast then
    cast:append(C.lua_pop(#vals_ast - #names_ast))
  end

  if ct_idx then
    -- activate closure scope (after having generated values)
    activate_closure_table(ct_idx)
  end

  -- store values in closure table and create local symbols
  for i=#names_ast,1,-1 do local name_ast = names_ast[i]
    local name = name_ast[1]

    if name_ast.upvalue then
      local varid = nextvarid()
      cast:append(C.lua_rawseti(realidx(ct_idx), varid))
      -- create local symbol
      currentscope[name] =
        {tag='Upval', ct_idx, currentscope['.closurelevel'], varid}
    end
  end
  -- create local symbols
  for i,name_ast in ipairs(names_ast) do
    local name = name_ast[1]; assert(name_ast.tag == 'Id')
    if not name_ast.upvalue then
      idxtop_change(1)
      currentscope[name] = idxtop
    end
  end
  return cast
end

-- Converts Lua `Set AST to C AST.
local function genset(stat_ast)
  -- note: supports x,y=y,x
  local ls_ast, rs_ast = stat_ast[1], stat_ast[2]
  local cast = cexpr()

  -- create values (r_ast)
  for i,r_ast in ipairs(rs_ast) do
    cast:append(genexpr(r_ast, 'onstack',
      #ls_ast > #rs_ast and i == #rs_ast and can_multi(r_ast) and
      (#ls_ast - #rs_ast + 1)))
  end

  -- cleanup if LHS and RHS lengths don't match
  if #ls_ast > #rs_ast and not can_multi(rs_ast[#rs_ast]) then
    cast:append(
      C.lua_settop(
        C.Op('+', C.lua_gettop(), #ls_ast - #rs_ast)))
  elseif #ls_ast < #rs_ast then
    cast:append(C.lua_pop(#rs_ast - #ls_ast))
  end

  for i=#ls_ast,1,-1 do
    cast:append(genlvalueassign(ls_ast[i]))
  end

  return cast
end

-- Converts Lua `Localrec AST to C AST.
local function genlocalrec(ast)
  local names_ast, vals_ast = ast[1], ast[2]
  assert(#names_ast == 1)
  assert(#vals_ast == 1)
  local name_ast = names_ast[1]
  local val_ast = vals_ast[1]
  assert(val_ast.tag == 'Function')

  local cast = cexpr()
  -- activate scope and symbol (prior to generating value)
  local ct_idx
  local varid
  local name = name_ast[1]
  if name_ast.upvalue then
    ct_idx = cast:append(gennewclosuretable()).idx
    activate_closure_table(ct_idx)
    -- create local symbol
    varid = nextvarid()
    currentscope[name] =
      {tag='Upval', ct_idx, currentscope['.closurelevel'], varid}
  else
    currentscope[name] = idxtop + 1
  end

  -- create value
  cast:append(genexpr(val_ast, 'onstack'))

  -- store value
  if name_ast.upvalue then
    cast:append(C.lua_rawseti(realidx(ct_idx), varid))
  else
    idxtop_change(1)
  end

  return cast
end

local function genstatement(stat_ast)
  local cast
  if stat_ast.tag == 'Set' then
    cast = genset(stat_ast)
  elseif stat_ast.tag == 'Return' then
    cast = cexpr()
    local can_multi = #stat_ast >= 1 and can_multi(stat_ast[#stat_ast])
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
  elseif stat_ast.tag == 'Repeat' then
    cast = genrepeat(stat_ast)
  elseif stat_ast.tag == 'Do' then
    cast = gendo(stat_ast)
  elseif stat_ast.tag == 'If' then
    cast = genif(stat_ast)
  elseif stat_ast.tag == 'Call' or stat_ast.tag == 'Invoke' then
    cast = genexpr(stat_ast, 'onstack', 0)
  elseif stat_ast.tag == 'Local' then
    cast = genlocalstat(stat_ast)
  elseif stat_ast.tag == 'Localrec' then
    cast = genlocalrec(stat_ast)
  elseif stat_ast.tag == 'Break' then
    cast = cexpr(C.Break())
  else
    assert(false, stat_ast.tag)
  end 

  assert(cast[1], table.tostring(cast))
  local comment = getlines(src, linerange(stat_ast))
  prependcomment(cast[1], comment)

  return cast
end

--local
function genblock(ast)
  local cast = cexpr()
  for _,stat_ast in ipairs(ast) do
    cast:append(genstatement(stat_ast))

    -- DEBUG
    if true then
      if funcinfo.is_vararg then
        funcinfo.is_lc_nextra_used_debug = true
      end
      if not is_created['assert.h'] then
        append_array(cast.pre, {C.Include'<assert.h>'})
        is_created['assert.h'] = true
      end
      cast:append(C.C(string.format([[assert(lua_gettop(L) %s== %d);]],
        funcinfo.is_lc_nextra_used_debug and "- lc_nextra " or "", idxtop)))
    end

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
static void lc_createarg(lua_State * L, const lc_args_t * const args) {
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

  const lc_args_t * const args = (lc_args_t*)lua_touserdata(L, 1);
  lc_createarg(L, args);

  lua_pushcfunction(L, traceback);

  /* note: IMPROVE: closure not always needed here */
  lua_newtable(L); /* closure table */
  lua_pushcclosure(L, lc_main, 1);
  int i;
  for (i=1; i < args->c; i++) {
    lua_pushstring(L, args->v[i]);
  }
  int status = lua_pcall(L, args->c-1, 0, -2);
  if (status != 0) {
    const char * msg = lua_tostring(L,-1);
    if (msg == NULL) msg = "(error object is not a string)";
    fputs(msg, stderr);
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


-- First pass through AST.
-- Each `Id node is marked with field upvalue = true if it is used as an
-- upvalue.
-- Each `Function node is marked with field uses_upvalue = true if it uses
-- at least one upvalue.
local function firstpass(ast)
  -- Represents current lexical scope.
  -- Maps variable name to variable info (see newvar).
  local scope = {}

  local functions = {}

  local function newscope()
    local saved_scope = scope
    scope = setmetatable({}, {__index=scope})
    return saved_scope
  end

  local function endscope(saved_scope)
    scope = assert(saved_scope)
  end

  local function newvar(id_ast)
    assert(id_ast.tag == 'Id', id_ast)
    local name = id_ast[1]
    scope[name] = {function_level = #functions, ast = id_ast}
  end

  local function usevar(name)
    local varinfo = scope[name]
    if varinfo and varinfo.function_level < #functions then
      --DEBUG('upval:', varinfo.ast)
      varinfo.ast.upvalue = true
      for i=varinfo.function_level+1,#functions do
        functions[i].uses_upvalue = true
      end
    end
  end

  local function process(ast)
    if ast.tag == nil or ast.tag == 'Do' then  -- block
      local saved_scope = newscope()
      for _,stat_ast in ipairs(ast) do
        process(stat_ast)
      end
      endscope(saved_scope)
    elseif ast.tag == 'Set' then
      for i=1,#ast[1] do process(ast[1][i]) end
      for i=1,#ast[2] do process(ast[2][i]) end
    elseif ast.tag == 'While' then
      process(ast[1])
      local saved_scope = newscope()
      process(ast[2])
      endscope(saved_scope)
    elseif ast.tag == 'Repeat' then
      local saved_scope = newscope()
      process(ast[1])
      process(ast[2])
      endscope(saved_scope)
    elseif ast.tag == 'If' then
      for i=1,#ast do
        if i % 2 == 0 or i == #ast then
          local saved_scope = newscope()
          process(ast[i])
          endscope(saved_scope)
        else
          process(ast[i])
        end      
      end
    elseif ast.tag == 'Fornum' then
      local saved_scope = newscope()
      newvar(ast[1])
      for i=2,#ast do process(ast[i]) end
      endscope(saved_scope)
    elseif ast.tag == 'Forin' then
      local saved_scope = newscope()
      for i=1,#ast[1] do newvar(ast[1][i]) end
      for i=1,#ast[2] do process(ast[2][i]) end
      process(ast[#ast])
      endscope(saved_scope)
    elseif ast.tag == 'Local' then
      if ast[2] then
        for i=1,#ast[2] do process(ast[2][i]) end
      end
      for i=1,#ast[1] do newvar(ast[1][i]) end
    elseif ast.tag == 'Localrec' then
      for i=1,#ast[1] do newvar(ast[1][i]) end
      if ast[2] then
        for i=1,#ast[2] do process(ast[2][i]) end
      end
    --metalua: elseif ast.tag == 'Goto' or ast.tag == 'Label' then
    elseif ast.tag == 'Return' then
      for i=1,#ast do process(ast[i]) end
    elseif ast.tag == 'Break' then
    elseif ast.tag == 'Nil' or ast.tag == 'Dots' or ast.tag == 'True'
           or ast.tag == 'False' or ast.tag == 'Number' or ast.tag == 'String'
    then
    elseif ast.tag == 'Function' then
      local saved_scope = newscope()
      table.insert(functions, ast)
      for i=1,#ast[1] do
        if ast[1][i].tag ~= 'Dots' then newvar(ast[1][i]) end
      end
      process(ast[2])
      table.remove(functions)
      endscope(saved_scope)
    elseif ast.tag == 'Table' then
      for i=1,#ast do process(ast[i]) end
    elseif ast.tag == 'Pair' then
      for i=1,2 do process(ast[i]) end
    elseif ast.tag == 'Op' then
      for i=2,#ast do process(ast[i]) end
    elseif ast.tag == 'Paren' then
      process(ast[1])
    -- metalua: elseif ast.tag == 'Stat' then
    elseif ast.tag == 'Call' then
      for i=1,#ast do process(ast[i]) end
    elseif ast.tag == 'Invoke' then
      process(ast[1])
      for i=3,#ast do process(ast[i]) end
    elseif ast.tag == 'Index' then
      for i=1,2 do process(ast[i]) end
    elseif ast.tag == 'Id' then
      usevar(ast[1])
    else
      assert(false,  ast.tag)
    end
  end


  process(ast)
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
  s = s:gsub('%/%*', '/ *')
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
--  DEBUG(type(cast) == 'table' and cast.tag or cast)
  if type(cast) ~= 'table' then
    if type(cast) =='number' then  -- convenience function
      local s =
        (cast ~= cast) and '(0.0/0.0)' or
        (cast ==  math.huge) and  'HUGE_VAL' or
        (cast == -math.huge) and '-HUGE_VAL' or
        tostring(cast)
      --note: HUGE_VAL/-HUGE_VAL defined in math.h

      --IMPROVE: avoid 'warning: integer constant is too large for
      -- "long" type', at least in gcc.  Make distinction between
      -- doubles and integers?
      --if not s:find('[Ee%.]') then
      --  s = s .. '.0'
      --end
      return s
    elseif type(cast) == 'string' then  -- convenience function
      return string.format("%q", cast):gsub('\\\n', '\\n')
    else
      assert(false, type(cast))
    end
  elseif cast.tag == 'C' or cast.tag == 'Id' then
    local ccode = cast[1]
    assert(type(ccode) == 'string', tostring(ccode))
    return ccode
  elseif cast.tag == 'Op' then
    local opid, a_cast, b_cast = cast[1], cast[2], cast[3]
    local pa,pz = '(', ')'  -- improve: sometimes can be avoided
    return pa .. cast_tostring(a_cast) ..
           ' ' .. opid .. ' ' .. cast_tostring(b_cast) .. pz
  elseif cast.tag == 'Include' then
    local name = cast[1]
    return '#include ' .. name
  elseif cast.tag == 'Let' then
    local id, val_cast = cast[1], cast[2]
    return "const int " .. id .. " = " .. cast_tostring(val_cast)
  elseif cast.tag == 'LetDouble' then
    local id, val_cast = cast[1], cast[2]
    return "const double " .. id .. " = " .. cast_tostring(val_cast)
  elseif cast.tag == 'LetMutableDouble' then
    local id, val_cast = cast[1], cast[2]
    return "double " .. id .. " = " .. cast_tostring(val_cast)
  elseif cast.tag == 'LetInt' then
    local id, val_cast = cast[1], cast[2]
    return "const int " .. id .. " = " .. cast_tostring(val_cast)
  elseif cast.tag == 'Enum' then
    local id, val_cast = cast[1], cast[2]
    return "enum { " .. id .. " = " .. tostring(val_cast) .. " }"
  elseif cast.tag == 'Not' then
    local a_ast = cast[1]
    local pa,pz = '(', ')'  -- improve: sometimes can be avoided
    return '!' .. pa .. cast_tostring(a_ast) .. pz
  elseif cast.tag == 'Return' then
    local a_ast = cast[1]
    return 'return' .. (a_ast and ' ' .. cast_tostring(a_ast) or '')
  elseif cast.tag == 'Break' then
    return 'break'
  elseif cast.tag == 'Call' then
    local args = {tag='C'}
    for i=2,#cast do
      args[#args+1] = cast_tostring(cast[i])
    end
    return cast[1] .. '(' .. table.concat(args, ',') .. ')'
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

local src_file = assert(io.open (src_filename, 'r'))
src            = src_file:read '*a'; src_file:close()
src = src:gsub('^#[^\r\n]*', '') -- remove any shebang

local ast      = mlc.ast_of_luastring (src)

firstpass(ast)

-- io.stderr:write(table.tostring(ast, "nohash", 60))

local cast = genfull(ast)

-- io.stderr:write(table.tostring(cast, "nohash", 60))

io.stdout:write(cast_tostring(cast))

