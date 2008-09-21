--
-- cast2string.lua
-- Converts C AST to C code string.
--
-- (c) 2008 David Manura.  Licensed in the same terms as Lua (MIT license).
-- See included LICENSE file for full licensing details.

local M = {}

local _G       = _G
local assert   = _G.assert
local ipairs   = _G.ipairs
local math     = _G.math
local string   = _G.string
local table    = _G.table
local tostring = _G.tostring
local type     = _G.type
local unpack   = _G.unpack

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
local function cast_to_string(cast)
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
    return pa .. cast_to_string(a_cast) ..
           ' ' .. opid .. ' ' .. cast_to_string(b_cast) .. pz
  elseif cast.tag == 'Include' then
    local name = cast[1]
    return '#include ' .. name
  elseif cast.tag == 'Let' then
    local id, val_cast = cast[1], cast[2]
    return "const int " .. id .. " = " .. cast_to_string(val_cast)
  elseif cast.tag == 'LetDouble' then
    local id, val_cast = cast[1], cast[2]
    return "const double " .. id .. " = " .. cast_to_string(val_cast)
  elseif cast.tag == 'LetMutableDouble' then
    local id, val_cast = cast[1], cast[2]
    return "double " .. id .. " = " .. cast_to_string(val_cast)
  elseif cast.tag == 'LetInt' then
    local id, val_cast = cast[1], cast[2]
    return "const int " .. id .. " = " .. cast_to_string(val_cast)
  elseif cast.tag == 'Enum' then
    local id, val_cast = cast[1], cast[2]
    return "enum { " .. id .. " = " .. tostring(val_cast) .. " }"
  elseif cast.tag == 'Not' then
    local a_ast = cast[1]
    local pa,pz = '(', ')'  -- improve: sometimes can be avoided
    return '!' .. pa .. cast_to_string(a_ast) .. pz
  elseif cast.tag == 'Return' then
    local a_ast = cast[1]
    return 'return' .. (a_ast and ' ' .. cast_to_string(a_ast) or '')
  elseif cast.tag == 'Break' then
    return 'break'
  elseif cast.tag == 'Call' then
    local args = {tag='C'}
    for i=2,#cast do
      args[#args+1] = cast_to_string(cast[i])
    end
    return cast[1] .. '(' .. table.concat(args, ',') .. ')'
  elseif cast.tag == 'CallL' then
    local args = {tag='C', 'L'}
    for i=2,#cast do
      args[#args+1] = cast_to_string(cast[i])
    end
    return cast[1] .. '(' .. table.concat(args, ',') .. ')'
  elseif cast.tag == 'Def' then
    local ts = {}
    for i,stat_cast in ipairs(cast) do
      ts[i] = cast_to_string(stat_cast) .. '\n\n'
    end
    local ccode = table.concat(ts)
    return ccode
  elseif cast.tag == nil then -- block
    local ts = {}
    if cast.comment then
      ts[#ts+1] = '\n' .. ccomment(cast.comment) .. '\n'
    end
    for i,stat_cast in ipairs(cast) do
      local comment = ''
      if stat_cast.comment then
        comment = '\n' .. ccomment(stat_cast.comment) .. '\n'
      end
      local postcomment = ''
      if stat_cast.postcomment then
        postcomment = ccomment(stat_cast.postcomment) .. '\n'
      end
      local semi = no_semicolon[stat_cast.tag] and '' or ';'
      ts[#ts+1] = comment .. cast_to_string(stat_cast) .. semi .. '\n' ..
              postcomment
    end
    if cast.postcomment then
      ts[#ts+1] = '\n' .. ccomment(cast.postcomment) .. '\n'
    end

    local ccode = indentcode(table.concat(ts))
    return ccode
  elseif cast.tag == 'If' then
    local ccode = ''
    for i=2,#cast,2 do
      if i ~= 2 then ccode = ccode .. 'else ' end
      ccode = ccode .. 'if (' .. cast_to_string(cast[i-1]) .. ') {\n' ..
              cast_to_string(cast[i]) .. '}'
    end
    if #cast % 2 == 1 then
      ccode = ccode .. '\nelse {\n' .. cast_to_string(cast[#cast]) .. '}'
    end
    return ccode
  elseif cast.tag == 'While' then
    local expr_cast, block_cast = cast[1], cast[2]
    local ccode = 'while (' .. cast_to_string(expr_cast) .. ') {\n' ..
                  cast_to_string(block_cast) .. '}'
    return ccode
  elseif cast.tag == 'Functiondef' then
    local id, body_cast = cast[1], cast[2]
    local comment = ''
    if cast.comment then
      comment = ccomment(cast.comment) .. '\n'
    end
    local postcomment = ''
    if cast.postcomment then
      postcomment = ccomment(cast.postcomment) .. '\n'
    end
    local ccode =
      comment ..
      'static int ' .. id .. ' (lua_State * L) {\n' ..
      cast_to_string(body_cast) .. '}\n' .. postcomment
    return ccode
  elseif cast.tag:find'lua_' == 1 then  -- convenience function
    return cast_to_string{tag='CallL', cast.tag, unpack(cast)}
  else
    assert(false, cast.tag)
  end
end
M.cast_to_string = cast_to_string

return M


