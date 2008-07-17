# Makefile for building in g++/gnumake.

LUA=./lua
CXX=g++
CXXFLAGS=-O2 -I$(LUA)/include -I$(LUA)/src -I.
LDFLAGS=-L$(LUA)/lib -L$(LUA)/src -llua

all :
	@echo nothing to do

# builds redistributable
TAG=`date +%Y-%m-%d|tr -d '-'`
dist :
	DIR=lua2c-$(TAG) ; \
	    (rm -fr $$DIR && \
	     mkdir $$DIR && \
	     mkdir $$DIR/examples && \
	     mkdir $$DIR/examples-lua && \
	     mkdir $$DIR/lib && \
	     mkdir $$DIR/lib/metalua && \
	     cp README LICENSE CHANGES Makefile lua2c lua2c.lua \
	       $$DIR && \
	     cp examples/*.lua $$DIR/examples/ && \
	     cp examples-lua/*.lua $$DIR/examples-lua/ && \
	     cp lib/*.lua $$DIR/lib/ && \
	     cp lib/metalua/*.lua $$DIR/lib/metalua/ && \
	     tar czvf $$DIR.tar.gz $$DIR )
