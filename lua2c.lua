-- lua2c - convert Lua source to C code.
--
-- WARNING: in development; many things are broken/unimplemented at this time.
--          a few things (upvalues/coroutines/tail cals) might remain
--          unimplemented--see hirsham's version:
--          http://lua-users.org/lists/lua-l/2006-07/msg00144.html
--
-- (c) 2008 David Manura.  Licensed under the same terms as Lua (MIT license).

package.path = package.path .. ';./lib/?.lua'

require "lexer"
require "gg"
require "mlp_lexer"
require "mlp_misc"
require "mlp_table"
require "mlp_meta"
require "mlp_expr"
require "mlp_stat"
require "mlp_ext"


if checkglobals then checkglobals() end

local mlc = { } 
_G.mlc = mlc
mlc.metabugs = false

  
function mlc.ast_of_luastring (src)
  local  lx  = mlp.lexer:newstream (src)
  local  ast = mlp.chunk (lx)
  return ast
end
   
function mlc.function_of_luastring (src)
  local  ast  = mlc.ast_of_luastring (src)
  local  func = mlc.function_of_ast(ast)
  return func
end

function mlc.function_of_luafile (name)
  local f   = io.open(name, 'r')
  local src = f:read '*a'
  f:close()
  return mlc.function_of_luastring (src, "@"..name)
end


local src_filename = ...

local src


-- forward declarations
local genexpr
local genblock

local indent = ''

-- C code currently being generated
local code = ''

-- C code currently being generated to place before 'code'.
-- e.g. forward declarations.
local precode = ''

-- Table of local variables.
-- Maps name -> stack index
local localvars = {}

-- topmost stack index
local idxtop = 0

local function printf(s, ...)
  code = code .. string.format(indent .. s .. "\n", ...)
end
local format = string.format

-- adjust stack index to relative (negative) position offset.
-- note: use only when values inside offset are on the stack (non-psuedoindices)
local function adjustidx(offset, idx)
  if idx > 0 then
    return idx
  else  --FIX:pseudoindices
    return idx + offset + 1
  end
end

-- Adjust stack relative indicies
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

-- Count number of temporary values on stack.
local function countstack(...)
  local n = select('#', ...)
  local ncount = 0
  for i=1,n do
    local idx = select(i, ...)
    if idx == -1 then ncount = ncount + 1 end
  end
  return ncount
end


--hack:IMPROVE?
--gets range of line numbers (first,last) represented by AST
--returns nothing if not information found.
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

local is_binopid = {
  ["add"]=true,
  ["sub"]=true,
  ["mul"]=true,
  ["div"]=true,
  ["mod"]=true,
  ["pow"]=true,
  ["concat"]=true,
  ["eq"]=true,
  ["lt"]=true,
  ["le"]=true,
  ["and"]=true,
  ["or"]=true
}
local is_unopid = {
  ["not"] = true,
  ["len"] = true,
  ["unm"] = true
}
local is_logicalop = {   -- returns boolean
  ["eq"]=true,
  ["lt"]=true,
  ["le"]=true,
  ["and"]=true,  -- conditionally
  ["or"]=true,
  ["not"]=true,
}

-- binary ops with metamethod behavior like "+"
local is_arithbinop = {
  ["add"]=true,
  ["sub"]=true,
  ["mul"]=true,
  ["div"]=true,
  ["mod"]=true,
  ["pow"]=true
}

local fops = {
  ["add"]=function(a,b) return a+b end,
  ["sub"]=function(a,b) return a-b end,
  ["mul"]=function(a,b) return a*b end,
  ["div"]=function(a,b) return a/b end,
  ["mod"]=function(a,b) return a%b end,
  ["pow"]=function(a,b) return a^b end,
  ["concat"]=function(a,b) return a..b end,
  ["eq"]=function(a,b) return a==b end,
  ["lt"]=function(a,b) return a<b end,
  ["le"]=function(a,b) return a<=b end,
  ["and"]=function(a,b) return a and b end,
  ["or"]=function(a,b) return a or b end,
  ["not"] = function(a) return not a end,
  ["len"] = function(a) return #a end,
  ["unm"] = function(a) return -a end
}


local opid_to_c = {
  ["add"]=function(a,b) return a .. ' + ' .. b end,
  ["sub"]=function(a,b) return a .. ' - ' .. b end,
  ["mul"]=function(a,b) return a .. ' * ' .. b end,
  ["div"]=function(a,b) return a .. ' / ' .. b end,
  ["mod"]=function(a,b) return a .. ' - floor(' .. a .. '/' .. b ..')*' .. b end,
          -- caution: a and b evaluate twice
  ["pow"]=function(a,b) return 'pow(' .. a .. ',' .. b .. ')' end,
          --FIX:includ math.h
  --["concat"]=function(a,b) return a..b end,
  --["eq"]=function(a,b) return a==b end,
  --["lt"]=function(a,b) return a<b end,
  --["le"]=function(a,b) return a<=b end,
  --["and"]=function(a,b) return a and b end,
  --["or"]=function(a,b) return a or b end,
  --["not"] = function(a) return not a end,
  --["len"] = function(a) return #a end,
  --["unm"] = function(a) return "-" .. a end
}

-- Convert Lua object to AST.
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
    assert(false, obj)
  end
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

-- Perform constant folding on AST
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

local function makebinop(opid)
  local old_code = code
  code = precode

  local indent_save = indent
  indent = ''
  printf([[
// warning: assumes indices in range LUA_REGISTRYINDEX < x < 0 are relative.
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
]], opid,
    assert(opid_to_c[opid])("lua_tonumber(L,idxa)", "lua_tonumber(L,idxb)"),
    opid, opid)
  indent = indent_save

  precode = code
  code = old_code
end

-- Maps function name to boolean indicated whether function has
-- been generated.
local is_created = {}

local function genarithbinop(ast, where)
  local opid, a_ast, b_ast = ast[1], ast[2], ast[3]

  local fname = "lc_" .. opid
  if not is_created[fname] then
    makebinop(opid)
    is_created[fname] = true
  end

  local a_idx = genexpr(a_ast, 'anywhere')
  local b_idx = genexpr(b_ast, 'anywhere')
  local nstack = countstack(a_idx, b_idx)
  a_idx, b_idx = adjustidxs(a_idx, b_idx)
  if nstack == 0 then
    printf("lua_pushnumber(L,lc_%s(L,%d,%d));", opid, a_idx, b_idx)
  else
    local id = nextid()
    printf("const double %s = lc_%s(L,%d,%d);", id, opid, a_idx, b_idx)
    printf("lua_pop(L,%d);", nstack)
    printf("lua_pushnumber(L,%s);", id)
  end

  return -1
end

--[[OLD:
local function genarithbinop(ast, where)
  local opid, a_ast, b_ast = ast[1], ast[2], ast[3]

  local a_idx, a_var
  if a_ast.tag ~= 'Number' then
    a_idx = genexpr(a_ast, 'anywhere')
    a_var = nextid()
    printf("const int %s = lua_isnumber(L,%d);", a_var, a_idx)
  end
  local b_idx, b_var
  if b_ast.tag ~= 'Number' then
    b_idx = genexpr(b_ast, 'anywhere')
    b_var = nextid()
    printf("const int %s = lua_isnumber(L,%d);", b_var, b_idx)
  end

  local nstack = (a_idx == -1 and 1 or 0) + (b_idx == -1 and 1 or 0)

  local a_idxold = a_idx
  if b_idx == -1 then
    a_idx = adjust_idx(-2, a_idx)
  end


  printf("if (%s && %s) {", a_var or '1', b_var or '1')
  local a_code = a_idx and format("lua_tonumber(L,%d)", a_idx) or a_ast[1]
  local b_code = b_idx and format("lua_tonumber(L,%d)", b_idx) or b_ast[1]
  local id = nextid()
  printf("  const lua_Number %s = %s;", id, opid_to_c[opid](a_code, b_code))
  if nstack ~= 0 then
    printf("  lua_pop(L, %d);", nstack)
  end
  printf("  lua_pushnumber(L,%s);", id)
  printf("}")
  printf("else {")

  local ts = {}
  if a_idx then
    ts[#ts+1] = format("luaL_getmetafield(L,%d,%q)", a_idx, '__' .. opid)
  end
  if b_idx then
    ts[#ts+1] = format("luaL_getmetafield(L,%d,%q)", b_idx, '__' .. opid)
  end
  printf("  if (%s) {", table.concat(ts, ' || '))
  printf("    lua_insert(L,%d);", -1 - nstack)
  if not a_idx then
    printf("    lua_pushnumber(L,%d);", a_ast[1])
    printf("    lua_insert(L,-2);")
  elseif a_idxold ~= -1 then
    printf("    lua_pushvalue(L,%d);", a_idx)
    printf("    lua_insert(L,-2);")
  end
  if not b_idx then
    printf("    lua_pushnumber(L,%d);", b_ast[1])
  elseif b_idx ~= -1 then
    printf("    lua_pushvalue(L,%d);", b_idx)
  end
  printf("    lua_call(L,2,1);")
  printf("  }")
  printf("  else {")
  -- note: Lua itself gives a more detailed error message.
  printf('    luaL_error(L, "attempt to perform arithmetic");')
  printf("  }")
  printf("}")

  return -1
end
]]

local function geneqop(ast, where)
  local a_ast, b_ast = ast[2], ast[3]
  local a_idx = genexpr(a_ast, where)
  local b_idx = genexpr(b_ast, where)
  local nstack = (a_idx == -1 and 1 or 0) + (b_idx == -1 and 1 or 0)
  a_idx, b_idx = adjustidxs(a_idx, b_idx)
  local var = nextid()
  printf("const int %s = lua_equal(L,%d,%d);", var, a_idx, b_idx)
  if nstack ~= 0 then
    printf("lua_pop(L,%d);", nstack)
  end
  printf("lua_pushboolean(L,%s);", var)
  return -1
end

local function genltop(ast, where)
  local opid, a_ast, b_ast = ast[1], ast[2], ast[3]

  local a_idx = genexpr(a_ast, 'anywhere')
  local b_idx = genexpr(b_ast, 'anywhere')
  local nstack = countstack(a_idx, b_idx)
  a_idx, b_idx = adjustidxs(a_idx, b_idx)

  local id = nextid()
  printf("const int %s = lua_lessthan(L,%d,%d);", id, a_idx, b_idx)

  if nstack ~= 0 then
    printf("lua_pop(L,%d);", nstack)
  end

  printf("lua_pushboolean(L,%s);", id)

  return -1
end

-- FIX: Implement <= op
-- Why does the Lua C API implement lua_lessthan but not lua_lessequal?
-- (note: lessqual is defined in lvm.c).
local function genleop(ast, where)
  assert(false, 'FIX: <= NOT IMPL')
  --FIX:TODO
end

local function genlogbinop(ast, where)
  local opid, a_ast, b_ast = ast[1], ast[2], ast[3]

  genexpr(a_ast, 'onstack')

  local s = opid == 'and' and '' or opid == 'or' and '! ' or assert(false)
  printf("if (%slua_toboolean(L,-1)) {", s)
  printf("  lua_pop(L,1);")
  indent = indent .. '  '
  genexpr(b_ast, 'onstack')
  indent = indent:sub(1,#indent-2)
  printf("}")

  return -1
end

local function gennotop(ast, where)
  local opid, a_ast = ast[1], ast[2]

  local a_idx = genexpr(a_ast, 'anywhere')

  printf("lua_pushboolean(L, ! lua_toboolean(L,%d));", a_idx)
  if a_idx == -1 then
    printf("lua_remove(L,-2);")
  end

  return -1
end


local function genconcatop(ast, where)
  local a_ast, b_ast = ast[2], ast[3]

  genexpr(a_ast, 'onstack')
  genexpr(b_ast, 'onstack')
  printf("lua_concat(L,2);")

  return -1
end

local function genfunction(ast, where)
  local params_ast, body_ast = ast[1], ast[2]

  --## generate function definition

  -- localize code
  local code_save = code
  local precode_save = precode
  code = ''
  precode = ''
  local localvars_save = localvars  --FIX:how to handle upvalues?
  local idxtop_old = idxtop
  idxtop = 0   -- FIX: currently assuming no upvalues
  localvars = {}

  for i,var_ast in ipairs(params_ast) do
    assert(var_ast.tag == 'Id')
    local varname = var_ast[1]
    localvars[varname] = i
    idxtop = idxtop + 1
  end

  local old_indent = indent
  indent = ''

  local comment = getlines(src, linerange(ast))
  comment = "// " .. comment:gsub("(\r?\n)", "%1" .. indent .. "// ")
  printf("%s", comment)  --IMPROVE:indent code style?

  local id = nextid()
  printf("static int %s(lua_State * L) {", id)
  indent = '  '
  genblock(body_ast)
  if #body_ast > 0 and body_ast[1].tag ~= 'Return' then
    printf("return 0;")
  end
  indent = ''
  printf("}")

  indent = old_indent

  localvars = localvars_save
  idxtop = idxtop_old
  precode = precode_save .. precode .. code
  code = code_save

  --## generate function object
  printf("lua_pushcfunction(L,%s);", id)

end

local function gentable(ast, where)
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
    printf("lua_newtable(L);")
  else
    printf("lua_createtable(L,%d,%d);",narr,nrec)
  end

  local pos = 0
  for _,e_ast in ipairs(ast) do
    if e_ast.tag == 'Pair' then
      local k_ast, v_ast = e_ast[1], e_ast[2]
      genexpr(k_ast, 'onstack')
      genexpr(v_ast, 'onstack')
      printf("lua_rawset(L,-3);")
    else
      genexpr(e_ast, 'onstack')
      pos = pos + 1
      printf("lua_rawseti(L,-2,%d);", pos)
    end
  end
  return -1
end

local function gencall(ast, where, nret)
  local isinvoke = ast.tag == 'Invoke'
  local iarg = isinvoke and 3 or 2

  -- whether last argument might possibly return multiple values
  local can_multret = #ast >= iarg and
    (ast[#ast].tag == 'Call' or ast[#ast].tag == 'Invoke')

  local id
  local function f()
    if can_multret then
      id = nextid()
      printf("const int %s = lua_gettop(L);", id)
    end
  end

  if isinvoke then
    local expr_ast, name_ast = ast[1], ast[2]  -- ...
    genexpr(expr_ast, 'onstack')
    f()
    genexpr(name_ast, 'onstack')
    printf("lua_gettable(L,-2);")
    printf("lua_insert(L,-2);")
  else
    assert(ast.tag == 'Call')
    local f_ast = ast[1]
    genexpr(f_ast, 'onstack')
    f()
  end

  for i=iarg,#ast do
    local ast2 = ast[i]
    genexpr(ast2, 'onstack', i == #ast and 'multret' or false)
  end
  local narg = can_multret and "lua_gettop(L)-" .. id or #ast-1
  if nret == 'multret' then
    printf("lua_call(L,%s,LUA_MULTRET);", narg, #ast-1)
  else
    printf("lua_call(L,%s,%d);", narg, nret or 1)
  end
  return -1
end

-- local
function genexpr(ast, where, nret)
  if ast.tag == 'Op' then
    ast = constant_fold(ast)
  end

  if ast.tag == 'Call' or ast.tag == 'Invoke' then
    return gencall(ast, where, nret)
  elseif ast.tag == 'Id' then
    local name = ast[1]
    if localvars[name] then -- local
      local idx = localvars[name]
      if where == 'anywhere' then
        return idx
      else
        printf("lua_pushvalue(L,%d);", idx)
      end
    else -- global
      printf("lua_getglobal(L,%q);", name)
    end
    return -1
  elseif ast.tag == 'Nil' then
    printf("lua_pushnil(L);")
    return -1
  elseif ast.tag == 'True' then
    printf("lua_pushboolean(L,1);")
    return -1
  elseif ast.tag == 'False' then
    printf("lua_pushboolean(L,0);")
    return -1
  elseif ast.tag == 'String' then
    local s = ast[1]
    s = s.format("%q", s):gsub('\\\n', '\\n')
    printf("lua_pushliteral(L,%s);", s)
    return -1
  elseif ast.tag == 'Number' then
    printf("lua_pushnumber(L,%g);", ast[1])
    return -1
  elseif ast.tag == 'Index' then
    local t_ast, k_ast = ast[1], ast[2]
    local t_idx = genexpr(t_ast, 'anywhere')
    genexpr(k_ast, 'onstack')
    printf("lua_gettable(L,%d);", adjustidx(-2, t_idx))
    if t_idx == -1 then
      printf("lua_remove(L,-2);")
    end
    return -1
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
  elseif ast.tag == 'Function' then
    return genfunction(ast, where)
  elseif ast.tag == 'Paren' then
    local ast2 = ast[1]
    return genexpr(ast2, where)
  elseif ast.tag == 'Table' then
    return gentable(ast, where)
  else
    assert(false, ast.tag)
  end
end

local function genlvalueassign(l_ast)
  if l_ast.tag == 'Id' then
    local name = l_ast[1]
    if localvars[name] then
      local l_idx = localvars[name]
      printf("lua_replace(L,%d);", l_idx)
    else  -- global
      printf("lua_setglobal(L,%q);", name)
    end
  elseif l_ast.tag == 'Index' then
    local t_ast, k_ast = l_ast[1], l_ast[2]
    local t_idx = genexpr(t_ast, 'anywhere')
    if t_idx == -1 then printf("lua_insert(L,-2);") end
    genexpr(k_ast, 'onstack')
    printf("lua_insert(L,-2);")
    printf("lua_settable(L,%d);", adjustidx(-3, t_idx))
    if t_idx == -1 then
      printf("lua_pop(L,1);")
    end
  else
    assert(false, l_ast.tag)
  end
end


local function genif(ast)
  assert(#ast == 3 or #ast == 2, 'FIX:UNIMPLEMENTED')
  local a_idx = genexpr(ast[1], 1, 'anywhere')
  printf("if (lua_toboolean(L,%d)) {", a_idx)

  indent = indent .. '  '
  local localvars_save = localvars
  localvars = newscope()
  genblock(ast[2])
  localvars = localvars_save
  indent = indent:sub(1,#indent-2)  

  if #ast == 2 then
    printf("}")
  else
    printf("}")
    printf("else {")

    indent = indent .. '  '
    local localvars_save = localvars
    localvars = newscope()
    genblock(ast[3])
    localvars = localvars_save
    indent = indent:sub(1,#indent-2)  

    printf("}")
  end

  if a_idx == -1 then
    printf("lua_pop(L,1);")
  end
end

local function genfornum(ast)
  local name_ast, e1_ast, e2_ast, e3_ast, block_ast =
    ast[1], ast[2], ast[3], ast[5] and ast[4] or ast[5], ast[5] or ast[4]
  local name_id = name_ast[1]; assert(name_ast.tag == 'Id')

  local var_id = nextid();
  local limit_id = nextid();
  local step_id = nextid();
  local var_idx = genexpr(e1_ast, 'anywhere')
  local limit_idx = genexpr(e2_ast, 'anywhere')
  local step_idx = e3_ast and genexpr(e3_ast, 'anywhere')

  local nstack = (var_idx   == -1 and 1 or 0) +
                 (limit_idx == -1 and 1 or 0) +
                 (step_idx  == -1 and 1 or 0)

  var_idx, limit_idx, step_idx = adjustidxs(var_idx, limit_idx, step_idx)

  local cond3 = step_idx and format(" && lua_isnumber(L,%d)", step_idx) or ""
  printf("if (!(lua_isnumber(L,%d) && lua_isnumber(L,%d)%s)) {",
     var_idx, limit_idx, cond3)
  printf("  luaL_error(L, \"'for' limit must be a number\");")
  printf("}")
  printf("double %s = lua_tonumber(L,%d);", var_id, var_idx)
  printf("const double %s = lua_tonumber(L,%d);", limit_id, limit_idx)
  if e3_ast then
    printf("const double %s = lua_tonumber(L,%d);", step_id, step_idx)
  else
    printf("const double %s = 1.0;", step_id)
  end

  printf("lua_pop(L,%d);", nstack)

  printf("while (%s > 0 && %s <= %s || %s <= 0 && %s >= %s) {",
         step_id, var_id, limit_id, step_id, var_id, limit_id)

  -- local scope to evaluate block
  local localvars_save = localvars
  localvars = newscope()
  local var_absidx = idxtop + 1
  localvars[name_id] = var_absidx

  indent = indent .. '  '
  printf("// local: %s at index %d", name_id, var_absidx)
  printf("lua_pushnumber(L, %s);", var_id)
  idxtop = idxtop + 1
  genblock(block_ast)
  printf("lua_pop(L, 1);")
  idxtop = idxtop - 1
  indent = indent:sub(1,#indent-2)
  localvars = localvars_save

  printf("  %s += %s;", var_id, step_id)
  printf("}")
 
end


local function genwhile(ast)
  local expr_ast, block_ast = ast[1], ast[2]

  local id = nextid()
  printf("const int %s = lua_gettop(L);", id)
  printf("while(1) {")
  indent = indent .. '  '
  do
    local expr_idx = genexpr(expr_ast, 'anywhere')
    printf("if (! lua_toboolean(L,%d)) {", expr_idx)
    if expr_idx == -1 then
      printf("  lua_pop(L,1);")
    end
    printf("  break;")
    printf("}")
    printf("lua_pop(L,1);")


    -- local scope to evaluate block
    local localvars_save = localvars
    localvars = newscope()
    genblock(block_ast)
    localvars = localvars_save
    printf("lua_settop(L,%s);", id)
  end
  indent = indent:sub(1,#indent-2)
  printf("}")
  printf("lua_settop(L,%s);", id)
end


local function gendo(ast)
  local id = nextid()
  printf("const int %s = lua_gettop(L);", id)
  printf("{")
  indent = indent .. '  '
  do
    -- local scope to evaluate block
    local localvars_save = localvars
    localvars = newscope()
    genblock(ast)
    localvars = localvars_save
    printf("lua_settop(L,%s);", id)
  end
  indent = indent:sub(1,#indent-2)
  printf("}")
  printf("lua_settop(L,%s);", id)
end


local function genlocalstat(ast)
  local names_ast, vals_ast = ast[1], ast[2]

  local id
  if #names_ast > #vals_ast then
    id = nextid()
    printf("const int %s = lua_gettop(L);",  id)
  end

  for i,val_ast in ipairs(vals_ast) do
    genexpr(val_ast, 'onstack', #names_ast > #vals_ast and i == #vals_ast and 'multret')
  end
  for i,name_ast in ipairs(names_ast) do
    local name = name_ast[1]; assert(name_ast.tag == 'Id')
    idxtop = idxtop + 1
    localvars[name] = idxtop
  end

  if #names_ast > #vals_ast then
    printf("lua_settop(L, %s + %d);", id, #names_ast)
  elseif #names_ast < #vals_ast then
    printf("lua_pop(L, %d);", #vals_ast - #names_ast)
  end
end

local function genstatement(stat_ast)
  local comment = getlines(src, linerange(stat_ast))
  comment = "// " .. comment:gsub("(\r?\n)", "%1" .. indent .. "// ")
  printf("%s", comment)  --IMPROVE:indent code style?

  if stat_ast.tag == 'Set' then
    -- note: supports x,y=y,x
    local l_ast, r_ast = stat_ast[1], stat_ast[2]
    for i=1,#r_ast do
      genexpr(r_ast[i], 'onstack')
    end
    for i=#r_ast,1,-1 do
      genlvalueassign(l_ast[i])
    end
  elseif stat_ast.tag == 'Return' then
    local can_multi = #stat_ast >= 1 and
      (stat_ast[#stat_ast].tag == 'Call' or stat_ast[#stat_ast].tag == 'Invoke')
    local id
    if can_multi then
      id = nextid()
      printf("const int %s = lua_gettop(L);", id)
    end
    for i,e_ast in ipairs(stat_ast) do
      genexpr(e_ast, 'onstack', i==#stat_ast and can_multi and 'multret' or 1)
    end
    if id then
      printf("return lua_gettop(L) - %s;", id)
    else
      printf("return %d;", #stat_ast)
    end
  elseif stat_ast.tag == 'Fornum' then
    genfornum(stat_ast)
  elseif stat_ast.tag == 'While' then
    genwhile(stat_ast)
  elseif stat_ast.tag == 'Do' then
    gendo(stat_ast)
  elseif stat_ast.tag == 'If' then
    genif(stat_ast)
  elseif stat_ast.tag == 'Call' or stat_ast.tag == 'Invoke' then
    genexpr(stat_ast, 'onstack', 0)
  elseif stat_ast.tag == 'Local' then
    genlocalstat(stat_ast)
  elseif stat_ast.tag == 'Localrec' then
    assert(false, 'FIX: Localrec NOT IMPL')
  elseif stat_ast.tag == 'Break' then
    printf("break;") --FIX: if any cleanup on scope exit needed
  else
    assert(false, stat_ast.tag)
  end 

  printf("")
end

--local
function genblock(ast)
  for _,stat_ast in ipairs(ast) do
    genstatement(stat_ast)
  end
end

local function genfull(ast)

  printf("int luamain(lua_State * L) {")
  indent = indent .. '  '
  genblock(ast)
  printf("")
  printf("return 0;")
  indent = indent:sub(1,#indent-2)
  printf("}")
  printf("")

  local usercode = precode .. code
  precode = ''
  code = ''


  printf("// WARNING: This file was automatically generated by Lua2C.");
  printf("")
  printf("#ifdef __cplusplus")
  printf('extern "C" {')
  printf("#endif")
  printf("#include <lua.h>")
  printf("#include <lauxlib.h>")
  printf("#include <lualib.h>")
  printf("#ifdef __cplusplus")
  printf("}")
  printf("#endif")
  printf("#include <stdio.h>")
  printf("#include <stdlib.h>")
  printf("")

  printf("%s", usercode)

  printf [[
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

]]


  printf [[
int pmain(lua_State * L) {
  luaL_openlibs(L);
  lua_pushcfunction(L, traceback);
  lua_pushcfunction(L, luamain);
  int status = lua_pcall(L, 0, 0, -2);
  if (status != 0) {
    fputs(lua_tostring(L,-1), stderr);
  }
  return 0;
}

int main() {
  lua_State * L = luaL_newstate();
  if (! L) { fputs("Failed creating Lua state.", stderr); exit(1); }

  int status = lua_cpcall(L, pmain, 0);
  if (status != 0) {
    fputs(lua_tostring(L,-1), stderr);
  }

  lua_close(L);
  return 0;
}
]]

end

local src_file = io.open (src_filename, 'r')
src            = src_file:read '*a'; src_file:close()
local ast      = mlc.ast_of_luastring (src)

--table.print(ast, "nohash", 40)

--genblock(ast)

genfull(ast)
print(code)

