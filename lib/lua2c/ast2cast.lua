--
-- ast2cast.lua
-- Converts Lua ASTs to C ASTs.
--
-- Variable naming conventions: ast (Lua AST), cast (C AST).
--
-- (c) 2008 David Manura.  Licensed in the same terms as Lua (MIT license).
-- See included LICENSE file for full licensing details.

--luaanalyze checks
--! local t_G = typeimport"luaanalyze.library.standard"
--! t_G.add_field "mlc"
--! t_G.add_field "mlp"
--! local ast_t = require "luaanalyze.type.ast"
--! ast_t.add_field "name"
--! ast_t.add_field "upvalue"
--! ast_t.add_field "idx"
--! ast_t.add_field "type"
--! typematch("[^c]ast$", ast_t) --FIX:match
--! checkglobals()
--! checktypes()

local M = {}

local _G           = _G
local assert       = _G.assert
local ipairs       = _G.ipairs
local math         = _G.math
local select       = _G.select
local setmetatable = _G.setmetatable
local string       = _G.string
local tostring     = _G.tostring
local type         = _G.type
local table        = _G.table
local unpack       = _G.unpack


-- converts Metalua AST <ast> built from string
-- <src> to C AST <cast>.
-- returns(cast)
local function ast_to_cast(src, ast)
--##------------------------------------------------------------------
--## Note: this is a large function nesting many closures;
--## indentation of its contents is omitted.
--##------------------------------------------------------------------


-- info on current scope. includes
-- table of local variables.
-- Maps name -> stack index
local _currentscope = {['.closurelevel'] = 0}

-- topmost stack index
local _idxtop = 0

local _names = {}

local _varid = 0

-- note: _is_created maps function name to boolean indicated whether
-- function has been generated.
local _is_created = {}


-- Information on function currently being compiled.
local _funcinfo = {is_vararg=false, nformalparams=0,
  is_lc_nextra_used=false, is_lc_nactualargs_used=false,
  is_lc_nextra_used_debug=false, is_lc_nactualargs_used_debug=false,
  idxtopmax = 0
  --old: outervars={}
}


-- LUA_MINSTACK value in luaconf.h
local LUA_MINSTACK = 20


-- Mutators for _idxtop.
local function idxtop_change(n)
  _idxtop = _idxtop + n
  _funcinfo.idxtopmax = math.max(_funcinfo.idxtopmax, _idxtop)
end
local function idxtop_restore(idx)
  assert(idx <= _idxtop)
  _idxtop = idx
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

-- remove whitespace from front and end of string
local function trim(s)
  return s:gsub('^%s+', ''):gsub('%s+$', '')
end

-- Prepends comment to comments above C AST node.
local function prepend_comment(cast, comment)
  local s = cast.comment and comment .. '\n' .. cast.comment or comment
  cast.comment = s
end

-- Appends comment to comments above C AST node.
local function append_comment(cast, comment)
  local s = cast.comment and cast.comment .. '\n' .. comment or comment
  cast.comment = s
end

-- Appends comment to comments after C AST node.
local function append_comment_below(cast, comment)
  local s = cast.aftercomment and cast.aftercomment .. '\n' ..
            comment or comment
  cast.aftercomment = s
end


-- Appends elements to array t2 to array t1.
local function append_array(t1,t2)
  for _,v in ipairs(t2) do t1[#t1+1] = v end
end

local function append_cast(cast1, cast2)
  if cast2.tag ~= nil then -- enclosing block omitted (convenience)
                           -- :IMPROVE: the convenience possibly isn't
                           -- worth the ambiguity. make separate function?
    assert(not cast2.pre)
    assert(not cast2.idx)
    cast2 = {cast2, pre=cast2.pre or {}, idx=nil}
  end
  append_array(cast1, cast2)
  if cast2.comment then
    if #cast2 > 0 then
      prepend_comment(cast2[1], cast2.comment)
    elseif #cast1 > 0 then
      append_comment_below(cast1[#cast1], cast2.comment)
    else
      assert(false)
    end
  end
  if cast2.aftercomment then
    if #cast2 > 0 then
      append_comment_below(cast2[#cast2], cast2.aftercomment)
    elseif #cast1 > 0 then
      append_comment_below(cast1[#cast1], cast2.aftercomment)
    else
      assert(false)
    end
  end
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

-- returns C AST of double for given C AST idx.
local function todouble(idx)
  if type(idx) == 'string' then
    return C.Id(idx)
  else
    return C.lua_tonumber(idx)
  end
end

-- returns C AST of bool for given C AST idx.
local function tobool(idx)
  if type(idx) == 'string' then
    return C.Id(idx)
  else
    return C.lua_toboolean(idx)
  end
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
  if _funcinfo.is_vararg and
     (tag(idxreal) == 'Id' or idxreal > _funcinfo.nformalparams)
  then
    if tag(idx) == 'Upval' then
      -- no adjustment
    else
      idx = C.Op('+', idx, C.Id'lc_nextra')
      _funcinfo.is_lc_nextra_used = true
    end
  end
  return idx
end

-- Gets real index of local var.
local function localidx(name)
  local idx = _currentscope[name]
  if not idx then return end

  return realidx(idx)
end


--old: local function isupvalue(name)
--  return not _currentscope[name] and _funcinfo.outervars[name]
--end

-- Adjusts stack index to relative (negative) position offset.  note:
-- use only when values inside offset are on the stack
-- (non-psuedoindices).
-- Note: allows C AST.
local function adjustidx(offset, idx)
  if type(idx) ~= 'number' or idx > 0 then
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
    if type(idx) == 'number' and idx < 0 then
            --FIX: and idx > LUA_REGISTRYINDEX ?
      result[i] = result[i] - nused   -- adjust
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

-- Given AST ast taken from inside code string src,
-- return code string representing AST.
local function get_ast_string(src, ast, ...)
  local first = ast.lineinfo.first[3]
  local last  = ast.lineinfo.last [3]
  local code = src:sub(first, last)
  return code
end

-- Gets next unique ID.  Useful for generating unique variable names.
-- orig_name is string of arbitrary text to base variable name
--   on (optional and may be ignored)
-- prefix is prefix string for variable (defaults to '')
local MAX_IDENTIFIER_LENGTH = 60 -- note: not a hard limit
local function nextid(orig_name, prefix)
  orig_name = orig_name or ''
  prefix = prefix or ''

  -- ensure will form a valid C identifier
  local name = orig_name:gsub('[^%w_]', '_')

  -- ensure uniqueness
  _names[name] = (_names[name] or 0) + 1

  local id =
    'lc' .. prefix .. _names[name] .. (name == '' and '' or '_') .. name
  return id
end

-- Gets next unique ID for lexical variable.
local function nextvarid()
  _varid = _varid + 1
  return _varid
end

local function newscope()
  local currentscope_old = _currentscope
  _currentscope = setmetatable({}, {__index = currentscope_old})
  return currentscope_old
end

local function restore_scope(currentscope_save)
  _currentscope = currentscope_save
end

local function restore_stack_rel(cast, idx_old)
  local npushed = _idxtop - idx_old
  if npushed ~= 0 then
    cast:append(C.lua_pop(npushed))
    append_comment(cast[#cast], 'internal: stack cleanup on scope exit')
  end
  idxtop_change(- npushed)
end

local function restore_stack_abs(cast, idx_old_cast, idx_old)
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

-- Deduce names of functions by the variables they are assigned to.
-- Given lists of LHS and RHS expressions, adds a "name" field
-- to any applicable RHS expression.
local function deduce_function_names(ls_ast, rs_ast)
  for i,r_ast in ipairs(rs_ast) do
    local l_ast = ls_ast[i]
    if ls_ast[i] and r_ast.tag == 'Function' then
      local name = get_ast_string(src, l_ast)
      r_ast.name = name
    end
  end
end


-- forward declarations
local genexpr
local genblock

-- Converts any Lua arithmetic op AST to C AST.
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
    if not _is_created['math.h'] then
      append_array(cast.pre, {C.Include'<math.h>'})
      _is_created['math.h'] = true
    end
  end

  local fname = "lc_" .. opid
  if not _is_created[fname] then
    append_array(cast.pre, {makebinop(opid)})
    _is_created[fname] = true
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

-- Converts Lua equality op AST to C AST.
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

-- Converts Lua less-than op AST to C AST.
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


-- Converts Lua less-than-or-equal op AST to C AST.
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
  if not _is_created[fname] then
    append_array(cast.pre, {makeop(opid)})
    _is_created[fname] = true
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

-- Converts Lua binary logical op AST to C AST.
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

-- Converts Lua unary logical (i.e. not) op AST to C AST.
local function gennotop(ast, where)
  local opid, a_ast = ast[1], ast[2]
  local cast = cexpr()

  local a_idx = cast:append(genexpr(a_ast, 'anywhere')).idx

  cast:append(C.lua_pushboolean(C.Not(tobool(a_idx))))
  if a_idx == -1 then
    cast:append(C.lua_remove(-2))
  end

  return cast
end

-- Converts Lua length op AST to C AST.
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


-- Converts Lua unary minus op AST to C AST.
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
  if not _is_created[fname] then
    append_array(cast.pre, {makeop()})
    _is_created[fname] = true
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

-- Converts Lua concatenation op AST to C AST.
local function genconcatop(ast, where)
  local a_ast, b_ast = ast[2], ast[3]
  local cast = cexpr()

  cast:append(genexpr(a_ast, 'onstack'))
  cast:append(genexpr(b_ast, 'onstack'))
  cast:append(C.lua_concat(2))

  return cast
end

-- Creates C AST for table used to manage upvalues
-- for a closure.
-- note: call activate_closure_table() afterward.
local function gennewclosuretable()
  local cast = cexpr()

  if not _is_created['lc_newclosuretable'] then
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

    _is_created['lc_newclosuretable'] = true
  end

  cast:append(C.CallL('lc_newclosuretable', get_closuretableidx_cast()))
  idxtop_change(1)

  local id = nextid()
  cast:append(C.Enum(id, _idxtop))
  if not _is_created['assert.h'] then
    append_array(cast.pre, {C.Include'<assert.h>'})
    _is_created['assert.h'] = true
  end
  cast:append(C.Call('assert', C.Op('==', C.lua_gettop(), realidx(C.Id(id)))))

  cast.idx = C.Id(id)

  return cast
end

local function activate_closure_table(idx)
  _currentscope['.closuretable'] = idx
  _currentscope['.closurelevel'] = _currentscope['.closurelevel'] + 1
end

-- Convert Lua `Function AST to C AST.
-- C AST defines the function's implementation.
-- helper function to generate function definition
-- is_main - whether this is the top-level "main" function.
local function genfunctiondef(ast, ismain)
  local params_ast, body_ast = ast[1], ast[2]

  -- localize new function info.
  local funcinfo_old = _funcinfo
  local has_vararg = params_ast[#params_ast]
                     and params_ast[#params_ast].tag == 'Dots'
  local nformalargs = #params_ast - (has_vararg and 1 or 0)
  _funcinfo = {is_vararg = has_vararg, nformalparams = nformalargs,
    is_lc_nextra_used = false, is_lc_nactualargs_used=false,
    is_lc_nextra_used_debug = false, is_lc_nactualargs_used_debug=false,
    idxtopmax = 0
    --old: outervars = _currentscope
  }

  -- note: special usage of _idxtop
  local idxtop_old = _idxtop
  _idxtop = 0

  -- localize code
  local currentscope_save = newscope()
  _currentscope['.closuretable'] = C.C'lua_upvalueindex(1)'

  -- define parameters as local variables.
  for i,var_ast in ipairs(params_ast) do
    if var_ast.tag ~= 'Dots' then
      assert(var_ast.tag == 'Id')
      local varname = var_ast[1]
      _currentscope[varname] = i
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
        _currentscope[name] =
          {tag='Upval', _idxtop, _currentscope['.closurelevel'], varid}

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
  if _funcinfo.idxtopmax + fudge >= LUA_MINSTACK then
    bodypre_cast:append(C.lua_checkstack(_funcinfo.idxtopmax + fudge))
  end

  -- note: do after generating body do that _funcinfo params are set
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
    if _funcinfo.is_lc_nextra_used then
      _funcinfo.is_lc_nactualargs_used = true
    elseif _funcinfo.is_lc_nextra_used_debug then
      _funcinfo.is_lc_nactualargs_used_debug = true
    end

    if _funcinfo.is_lc_nactualargs_used then
      bodypre_cast:append(C.LetInt('lc_nactualargs', C.lua_gettop()))
    elseif _funcinfo.is_lc_nactualargs_used_debug then
      bodypre_cast:append(C.C'#ifndef NDEBUG')
      bodypre_cast:append(C.LetInt('lc_nactualargs', C.lua_gettop()))
      bodypre_cast:append(C.C'#endif')
    end
    if _funcinfo.is_lc_nextra_used then
      bodypre_cast:append(C.LetInt('lc_nextra',
        C.Op('-', C.Id'lc_nactualargs', C.Id'lc_nformalargs')))
    elseif _funcinfo.is_lc_nextra_used_debug then
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

  local id = ast.is_main and 'lcf_main'
             or nextid(ast.name, 'f')
  local def_cast = cexpr()
  append_array(def_cast, body_cast.pre)
  local func_cast = C.Functiondef(id, body_cast)

  local comment =
    ast.is_main and '(...)' or
    trim(src:sub(ast.lineinfo.first[3], params_ast.lineinfo.last[3])) .. ')'
  if comment:sub(1,1) == '(' then
    comment = 'function' .. comment
  end
  if ast.name then
    comment = 'name: ' .. ast.name .. '\n' .. comment
  end
  func_cast.comment = comment

  func_cast.id = id
  append_array(def_cast, { func_cast })

  restore_scope(currentscope_save)
  _idxtop = idxtop_old

  _funcinfo = funcinfo_old

  return def_cast
end

-- Converts Lua `Function AST to C AST.
-- The C AST instantiates the function/closure (and includes code to define
-- the function implementation also).
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

-- Convert Lua top-level block AST (for top-level main function)
-- to C AST.
local function genmainchunk(ast)
  local astnew = {tag='Function', is_main=true, name='(main)', {{tag='Dots'}},
    ast, lineinfo=ast.lineinfo} -- note: lineinfo not cloned. ok?

  return genfunctiondef(astnew, true)
end


-- Converts Lua `Table AST to C AST.
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

-- Converts Lua `Call or `Invoke AST to C AST.
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
  if not _is_created['lc_setupvalue'] then
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
    _is_created['lc_setupvalue'] = true
  end
  return cast
end

-- helper
local function gen_lc_getupvalue(tidx, level, varid)
  assert(tidx and level and varid)
  local cast = cexpr(C.CallL('lc_getupvalue', tidx, level, varid))
  if not _is_created['lc_getupvalue'] then
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
    _is_created['lc_getupvalue'] = true
  end
  return cast
end

-- Converts Lua `Number AST to C C AST
local function gennumber(x, pre_cast)
  if x == math.huge or x == -math.huge then
    if not _is_created['math.h'] then
      append_array(pre_cast, {C.Include'<math.h>'})
      _is_created['math.h'] = true
    end
  end
  return x
end

-- Converts any Lua expression AST to C AST.
-- (local)
function genexpr(ast, where, nret)
  if ast.tag == 'Op' then
    ast = constant_fold(ast)
  end

  if ast.tag == 'Nil' then
    return cexpr(C.lua_pushnil())
  elseif ast.tag == 'Dots' then
    if nret == 'multret' then
      _funcinfo.is_lc_nactualargs_used = true
      return cexpr(C.C[[{int i; for (i=lc_nformalargs+1; i<=lc_nactualargs; i++) { lua_pushvalue(L, i); }}]])
    elseif nret and nret > 1 then
      _funcinfo.is_lc_nextra_used = true
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
    if _currentscope[name] then -- local
      local idx = localidx(name)
      if tag(idx) == 'Upval' then
        local closuretable_idx, closurelevel, varid = idx[1], idx[2], idx[3]
        cast:append(gen_lc_getupvalue(
          get_closuretableidx_cast(),
          _currentscope['.closurelevel'] - closurelevel, varid))
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

-- Converts Lua l-value expression AST to C AST.
local function genlvalueassign(l_ast)
  local cast = cexpr()
  if l_ast.tag == 'Id' then
    local name = l_ast[1]
    if _currentscope[name] then
      local idx = localidx(name)
      if tag(idx) == 'Upval' then
        local closuretable_idx, closurelevel, varid = idx[1], idx[2], idx[3]
        cast:append(gen_lc_setupvalue(
          get_closuretableidx_cast(),
          _currentscope['.closurelevel'] - closurelevel, varid))
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


-- Converts Lua `If AST to C AST.
local function genif(ast, i)
  i = i or 1  -- i > 1 is index in AST node of elseif branch to generate
  local cast = cexpr()
  local if_args = {pre=cast.pre}

  local currentscope_save = _currentscope

  local base_idx = _idxtop
  local base_id = nextid()
  cast:append(C.Enum(base_id, base_idx))

  do
    local expr_ast, body_ast = ast[i], ast[i+1]

    idxtop_restore(base_idx)

    -- expression
    local a_idx = cast:append(genexpr(expr_ast, 'anywhere')).idx
    if a_idx ~= -1 then
      if_args[#if_args+1] = tobool(a_idx)
    else
      local id = nextid();
      cast:append(C.Let(id, tobool(-1)))
      cast:append(C.lua_pop(1))
      if_args[#if_args+1] = C.Id(id)
    end

    -- block
    newscope()
    local block_cast = genblock(body_ast)
    table.insert(if_args, block_cast)
    append_array(cast.pre, block_cast.pre)
    restore_scope(currentscope_save)
  end

  if ast[i+2] then
    idxtop_restore(base_idx)

    local currentscope_save = newscope()
    local block_cast
    if not ast[i+3] then
      block_cast = genblock(ast[i+2])
      if block_cast[1] then
        prepend_comment(block_cast[1], 'else')
      end
    else
      block_cast = genif(ast, i+2)
    end
    table.insert(if_args, block_cast)
    append_array(cast.pre, block_cast.pre)
    restore_scope(currentscope_save)
  end
  -- note: idx is (in general) indeterminant now
  -- due to the multiple branches.

  cast:append(C.If(unpack(if_args)))

  cast:append(C.lua_settop(realidx(C.Id(base_id))))
  idxtop_restore(base_idx)

  local start =
    i == 1 and ast.lineinfo.first[3] or ast[i-1].lineinfo.last[3]+1
  prepend_comment(cast, trim(src:sub(start, ast[i].lineinfo.last[3])) ..
                          ' then')
  if i == 1 then
    append_comment_below(cast, 'end')
  end
  local comment = false

  return cast, comment
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
  cast:append(C.LetMutableDouble(var_id, todouble(var_idx)))
  cast:append(C.LetDouble(limit_id, todouble(limit_idx)))
  if e3_ast then
    cast:append(C.LetDouble(step_id, todouble(step_idx)))
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

  local base_idx = _idxtop
  local base_id = nextid()
  cast:append(C.Enum(base_id, base_idx))

  -- create local
  if name_ast.upvalue then
    local ct_idx = block_cast:append(gennewclosuretable()).idx
    activate_closure_table(ct_idx)

    local varid = nextvarid()
    block_cast:append(C.lua_pushnumber(C.Id(var_id)))
    block_cast:append(C.lua_rawseti(-2, varid))
    _currentscope[name_id] =
      {tag='Upval', ct_idx, _currentscope['.closurelevel'], varid}
  else
    block_cast:append(C.lua_pushnumber(C.Id(var_id)))
    idxtop_change(1)
    _currentscope[name_id] = _idxtop
  end
  block_cast[1].comment =
    string.format("internal: local %s at index %d", name_id, _idxtop)

  block_cast:append(genblock(block_ast))

  restore_stack_rel(block_cast, base_idx)
  restore_scope(currentscope_save)

  block_cast:append(C.C(var_id .. ' += ' .. step_id .. ';')) --IMPROVE?

  cast:append(C.While(while_expr_cast, block_cast))
  append_array(cast.pre, block_cast.pre)

  -- note: mixed breaks and locals can leave the stack at an
  -- unknown size, so absolute adjust here.
  restore_stack_abs(cast, C.Id(base_id), base_idx)

  prepend_comment(cast,
    trim(src:sub(ast.lineinfo.first[3], block_ast.lineinfo.first[3]-1)))
  append_comment_below(cast, 'end')
  local comment = false

  return cast, comment
end

-- Converts Lua `Forin AST to C AST.
local function genforin(ast)
  local names_ast, exprs_ast, block_ast = ast[1], ast[2], ast[3]
  local cast = cexpr()

  local multi = can_multi(exprs_ast[1])

  local base_idx = _idxtop
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
  append_comment(cast[1], 'internal: local f, s, var = explist')

  local base2_idx = _idxtop

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
    append_comment(block_cast[#block_cast],
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
    local idx1 = _idxtop - #names_ast
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
          _currentscope[name_id] =
            {tag='Upval', ct_idx, _currentscope['.closurelevel'], varids[i]}
        else
          nlocals = nlocals + 1
        end
      end
      for i,name_ast in ipairs(names_ast) do if varids[i] then
        append_comment(block_cast[pos1+1],
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
          _currentscope[name_id] = idx1 + count
          append_comment(block_cast[pos1+1],
            string.format("internal: local %s with idx %d",
                          name_id, _currentscope[name_id]))
        end
      end
    end

    -- block
    block_cast:append(genblock(block_ast))

    -- end scope
    restore_stack_rel(block_cast, base2_idx)
    restore_scope(currentscope_save)
  end
  cast:append(C.While(1, block_cast))
  append_array(cast.pre, block_cast.pre)

  restore_stack_abs(cast, C.Id(base_id), base_idx)

  prepend_comment(cast,
    trim(src:sub(ast.lineinfo.first[3], block_ast.lineinfo.first[3]-1)))
  append_comment_below(cast, 'end')
  local comment = false

  return cast, comment
end


-- Converts Lua `While AST to C AST.
local function genwhile(ast)
  local expr_ast, block_ast = ast[1], ast[2]
  local cast = cexpr()

  local base_idx = _idxtop
  local base_id = nextid()
  cast:append(C.Enum(base_id, base_idx))

  do
    -- expression
    local block_cast = cexpr(); do
      local expr_idx = block_cast:append(genexpr(expr_ast, 'anywhere')).idx
      block_cast:append(
        C.If(C.Not(tobool(expr_idx)), {C.Break()}))
      if expr_idx == -1 then
        block_cast:append(C.lua_pop(1))
      end

      -- local scope to evaluate block
      local currentscope_save = newscope()

      -- block
      block_cast:append(genblock(block_ast))

      restore_stack_rel(block_cast, base_idx)
      restore_scope(currentscope_save)
    end

    cast:append(C.While(1, block_cast))
    append_array(cast.pre, block_cast.pre)
  end

  -- note: mixed breaks and locals can leave the stack at an
  -- unknown size, so absolute adjust here.
  restore_stack_abs(cast, C.Id(base_id), base_idx)

  prepend_comment(cast,
    trim(src:sub(ast.lineinfo.first[3], block_ast.lineinfo.first[3]-1)))
  append_comment_below(cast, 'end')
  local comment = false

  return cast, comment
end


-- Converts Lua `Repeat AST to C AST.
local function genrepeat(ast)
  local block_ast, expr_ast = ast[1], ast[2]
  local cast = cexpr()

  local base_idx = _idxtop
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
        C.If(tobool(expr_idx), {C.Break()}))

      restore_stack_rel(block_cast, base_idx)
      restore_scope(currentscope_save)
    end
    cast:append(C.While(1, block_cast))
    append_array(cast.pre, block_cast.pre)
  end

  -- note: mixed breaks and locals can leave the stack at an
  -- unknown size, so absolute adjust here.
  restore_stack_abs(cast, C.Id(base_id), base_idx)

  prepend_comment(cast, 'repeat')
  append_comment_below(cast,
    trim(src:sub(block_ast.lineinfo.last[3]+1, ast.lineinfo.last[3])))
  local comment = false

  return cast, comment
end


-- Converts Lua `Do AST to C AST.
local function gendo(ast)
  local cast = cexpr()

  local base_idx = _idxtop

  -- local scope to evaluate block
  local currentscope_save = newscope()
  cast:append(genblock(ast))
  restore_scope(currentscope_save)
  restore_stack_rel(cast, base_idx)

  prepend_comment(cast, 'do')
  append_comment_below(cast, 'end')
  local comment = false

  return cast, comment
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

  deduce_function_names(names_ast, vals_ast)

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
      _currentscope[name] =
        {tag='Upval', ct_idx, _currentscope['.closurelevel'], varid}
    end
  end
  -- create local symbols
  for i,name_ast in ipairs(names_ast) do
    local name = name_ast[1]; assert(name_ast.tag == 'Id')
    if not name_ast.upvalue then
      idxtop_change(1)
      _currentscope[name] = _idxtop
    end
  end
  return cast
end

-- Converts Lua `Set AST to C AST.
local function genset(stat_ast)
  -- note: supports x,y=y,x
  local ls_ast, rs_ast = stat_ast[1], stat_ast[2]
  local cast = cexpr()

  deduce_function_names(ls_ast, rs_ast)

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
    _currentscope[name] =
      {tag='Upval', ct_idx, _currentscope['.closurelevel'], varid}
  else
    _currentscope[name] = _idxtop + 1
  end

  deduce_function_names(names_ast, vals_ast)

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

-- Converts any Lua statement AST to C AST.
local function genstatement(stat_ast)
  local cast
  local comment
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
    cast, comment = genfornum(stat_ast)
  elseif stat_ast.tag == 'Forin' then
    cast, comment = genforin(stat_ast)
  elseif stat_ast.tag == 'While' then
    cast, comment = genwhile(stat_ast)
  elseif stat_ast.tag == 'Repeat' then
    cast, comment = genrepeat(stat_ast)
  elseif stat_ast.tag == 'Do' then
    cast, comment = gendo(stat_ast)
  elseif stat_ast.tag == 'If' then
    cast, comment = genif(stat_ast)
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
  if comment ~= false then
    comment = comment or get_ast_string(src, stat_ast)
    prepend_comment(cast, comment)
  end
  return cast
end

-- Converts Lua block AST to C AST.
-- (local)
function genblock(ast)
  local cast = cexpr()
  for _,stat_ast in ipairs(ast) do
    local stat_cast = genstatement(stat_ast)

    local comments = stat_ast.lineinfo.first.comments
    if comments then
      for i=#comments,1,-1 do
        local comment = src:sub(comments[i][2], comments[i][3]):gsub('\n$','')
        prepend_comment(stat_cast, comment)
      end
    end

    cast:append(stat_cast)

    -- DEBUG
    if true then
      if _funcinfo.is_vararg then
        _funcinfo.is_lc_nextra_used_debug = true
      end
      if not _is_created['assert.h'] then
        append_array(cast.pre, {C.Include'<assert.h>'})
        _is_created['assert.h'] = true
      end
      cast:append(C.C(string.format([[assert(lua_gettop(L) %s== %d);]],
        _funcinfo.is_lc_nextra_used_debug and "- lc_nextra " or "", _idxtop)))
    end

  end

  if #ast > 0 then
    local stat_ast = ast[#ast]
    local comments = stat_ast.lineinfo.last.comments
    if comments then
      for i=1,#comments do
        local comment = src:sub(comments[i][2], comments[i][3]):gsub('\n$','')
        append_comment_below(cast[#cast], comment)
      end
    end
  else
    local comments = ast.lineinfo.first.comments
    if comments then
      for i=1,#comments do
        local comment = src:sub(comments[i][2], comments[i][3]):gsub('\n$','')
        append_comment_below(cast, comment)
      end
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


-- Converts Lua top-level function to C AST,
-- including prelude.
local function genfull(ast)
  -- support LUA_INIT environment variable
  local enable_lua_init = true

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

  if enable_lua_init then
    cast:append(C.C [[
#include <string.h>
]])
  end

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

  if enable_lua_init then
    cast:append(C.C [[
static void lc_l_message (const char *pname, const char *msg) {
  if (pname) fprintf(stderr, "%s: ", pname);
  fprintf(stderr, "%s\n", msg);
  fflush(stderr);
}

static int lc_report (lua_State *L, int status) {
  if (status && !lua_isnil(L, -1)) {
    const char *msg = lua_tostring(L, -1);
    if (msg == NULL) msg = "(error object is not a string)";
    /*FIX-IMROVE:progname*/
    lc_l_message("lua", msg);
    lua_pop(L, 1);
  }
  return status;
}

static int lc_docall (lua_State *L, int narg, int clear) {
  int status;
  int base = lua_gettop(L) - narg;  /* function index */
  lua_pushcfunction(L, traceback);  /* push traceback function */
  lua_insert(L, base);  /* put it under chunk and args */
  /*FIX? signal(SIGINT, laction); */
  status = lua_pcall(L, narg, (clear ? 0 : LUA_MULTRET), base);
  /*FIX? signal(SIGINT, SIG_DFL); */
  lua_remove(L, base);  /* remove traceback function */
  /* force a complete garbage collection in case of errors */
  if (status != 0) lua_gc(L, LUA_GCCOLLECT, 0);
  return status;
}

static int lc_dofile (lua_State *L, const char *name) {
  int status = luaL_loadfile(L, name) || lc_docall(L, 0, 1);
  return lc_report(L, status);
}

static int lc_dostring (lua_State *L, const char *s, const char *name) {
  int status = luaL_loadbuffer(L, s, strlen(s), name) || lc_docall(L, 0, 1);
  return lc_report(L, status);
}

static int lc_handle_luainit (lua_State *L) {
  const char *init = getenv(LUA_INIT);
  if (init == NULL) return 0;  /* status OK */
  else if (init[0] == '@')
    return lc_dofile(L, init+1);
  else
    return lc_dostring(L, init, "=" LUA_INIT);
}
]])
  end

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

  cast:append(C.C([[
static int lc_pmain(lua_State * L) {
  luaL_openlibs(L);

  const lc_args_t * const args = (lc_args_t*)lua_touserdata(L, 1);
  lc_createarg(L, args);

  lua_pushcfunction(L, traceback);

]] .. (
  enable_lua_init and [[
  const int status1 = lc_handle_luainit(L);
  if (status1 != 0) return 0;
]] or '') ..
[[

  /* note: IMPROVE: closure not always needed here */
  lua_newtable(L); /* closure table */
  lua_pushcclosure(L, lcf_main, 1);
  int i;
  for (i=1; i < args->c; i++) {
    lua_pushstring(L, args->v[i]);
  }
  int status2 = lua_pcall(L, args->c-1, 0, -2);
  if (status2 != 0) {
    const char * msg = lua_tostring(L,-1);
    if (msg == NULL) msg = "(error object is not a string)";
    fputs(msg, stderr);
  }
  return 0;
}
]]))

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
M.genfull = genfull


-- First pass through AST <ast>.
-- Each `Id node is marked with field <upvalue=true> if it is used as an
-- upvalue.
-- Each `Function node is marked with field <uses_upvalue=true> if it uses
-- at least one upvalue.
local function first_pass(ast)
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


first_pass(ast)

local cast = genfull(ast)

return cast


--##------------------------------------------------------------------
--## Note: this is a large function nesting many closures;
--## indentation of its contents is omitted.
--##------------------------------------------------------------------
end
-- end of ast_to_cast


M.ast_to_cast = ast_to_cast

return M
