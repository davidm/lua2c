lua2c - converts Lua 5.1 source code to C code.

== Description ==

This utility converts a given Lua source file into an equivalent C
source file written in terms of Lua C API calls.  At least, this works
for a large subset of the Lua language (see limitations below).

The compiler is written entirely in Lua, and no build/install is
needed.  This project reuses Metalua's gg/mlp parser to convert Lua
source to a Metalua-style [1] AST over which the compiler then
operates.  lua2c does not require Metalua itself though since gg/mlp
is bundled in the distribution and is written in pure Lua.

== Usage ==

Example usage:

  lua lua2c.lua test/bisect.lua

which generates a C file to standard output.

You may also use the shell script "clua" to compile Lua->C->machine
code and execute all in one step.  However, you may need to edit the
variables in the file to match your system since this utility invokes
the C compiler.

  ./clua test/bisect.lua

lua2c can even compile itself!  (Note: the -c option compiles only
without running.)

  ./clua -c lua2c.lua               # compile lua2c binary

  ./lua2c examples-lua/bisect.lua   # test

== Related Work ==

  * luac2c - This related effort by Hisham Muhammad [2] converts Lua
    bytecodes to C source, whereas this project converts Lua
    source to C source.  luac2c runs into a few similar
    limitations as given below.  luac2c has remained experimental but
    superseded Luiz Henrique De Figueiredo's very basic but similarly
    named lua2c for Lua 4.0 [3].

  * luagen++ [4] uses C++ expression templates to translate
    Lua-like C++ statements to C API calls.  Some of the code
    generation structure is actually fairly similar to lua2c.

  * Python Pyrex [5] does something similar in Python but has the
    added goal of lowering the boundary between C and Python
    code.  Something like that could be done with lua2c,
    especially since lua2c uses the extensible gg parser.

  * Clue by David Given [6] does the opposite: convert C source
    to Lua source.

  * luac + BinToCee allow compilation of Lua source to bytecodes
    and/or embedding in a C file.

== Potential Uses ==

I think this project not only is theoretically nice to have but
has a number of potential uses:

  * Provide another approach of compiling Lua to machine code
    (rather than luac + bin2c).

  * Streamline the interface between C and Lua code and allow
    efficient access to C datatypes from Lua (see Pyrex above).

  * Compile Lua to optimized C.  For example, by statically
    determining that certain variables are used in a restricted
    way (e.g. by decorating the Lua source file with pragmas or
    determining this implicitly by inference), certain code
    constructs might be simplified to use plain C rather that
    the Lua C API.  This could allow certain Lua code written
    with sufficient care to run at native speeds.  Since it compiles
    to C, it will even work on CPUs where LuaJIT is not available.

== Limitations / Status ==

WARNING: This code passes much of the Lua 5.1 test suite [7] and can
compile itself, but the code is new and there can still be errors.
In particular, a few language features (e.g. coroutines) are not
implemented.  See comments in lua2c.lua for details.  Please report
bugs/patches on the wiki.

lua2c does not currently support coroutines, functions that normally
reject C functions (e.g. setfenv), and possibly tail call
optimizations.  Not all of these have the exact analogue in C.
Coroutines might not ever be supported. However, some solutions might
be explored [8][9], including possibly generating code that maintains
the coroutine context in Lua tables.

Closures and upvalues are implemented, but creating and accessing
upvalues is somewhat slow due to the implementation (see implementation
notes below) and hopefully can be improved.

Once the code is more complete/robust, more attention can be given to
optimizing the code generation.  Performance was 25%-75% of regular
Lua when running a few tests [11], but hopefully future optimizations
will improve that.

== Lua 5.2 Notes ==

Note: LuaFiveTwo (as of 5.2.0-work4) deprecates getfenv and setfenv,
which eliminates one of the limitations above. LuaFiveTwo has new lua_arith
and lua_compare C API function, which eliminate the need for lua2c to
reimplement these functions. LuaFiveTwo also has new lua_yieldk, lua_callk,
and lua_pcallk functions for coroutines and might help to implement
coroutines in lua2c. 

== Project Page ==

The project page is currently http://lua-users.org/wiki/LuaToCee .

== Download ==

  * Latest development source (recommended): http://github.com/davidm/lua2c/ .
    From here you can browse the source, download a tar/zip snapshot, or
    checkout with git by running "{{git clone
    git://github.com/davidm/lua2c.git}}".
  * Last release distribution: (see Project Page above)

== Licensing ==

(c) 2008 David Manura.  Licensed under the same terms as Lua (MIT
license).  See included LICENSE file for full licensing details.
Please post any patches/improvements.

== References ==

  * [1] Metalua AST - http://metalua.luaforge.net/manual006.html#toc17
  * [2] luac2c (previously named luatoc) - LuaList:2006-07/msg00144.html
  * [3] LHF's lua2c for Lua 4.0 - LuaList:2002-01/msg00296.html
  * [4] luagen++ - LuaGenPlusPlus
  * [5] Pyrex - http://www.cosc.canterbury.ac.nz/greg.ewing/python/Pyrex/
  * [6] Clue - http://cluecc.sourceforge.net/
  * [7] Lua 5.1 test suite -
        http://www.inf.puc-rio.br/~roberto/lua/lua5.1-tests.tar.gz
  * [8] Wikipedia:Coroutine - Implementations for C
        http://en.wikipedia.org/wiki/Coroutine#Implementations_for_C
  * [9] Coco - http://luajit.org/coco.html Coco -
        True C coroutine semantics (used in LuaJIT)
  * [10] BinToCee - http://lua-users.org/wiki/BinToCee
  * [11] The Computer Language Benchmarks Game
         http://shootout.alioth.debian.org/gp4/lua.php
  * http://lua-users.org/wiki/LuaImplementations -
         other source translators and Lua reimplementations
