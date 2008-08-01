# Makefile for building in g++/gnumake.

all :
	@echo nothing to do

# builds redistributable
TAG=`date +%Y-%m-%d|tr -d '-'`
dist :
	DIR=lua2c-$(TAG) ; \
	    (rm -fr $$DIR && \
	     mkdir $$DIR && \
	     mkdir $$DIR/examples-lua && \
	     mkdir $$DIR/lib && \
	     mkdir $$DIR/lib/metalua && \
	     cp README LICENSE CHANGES Makefile lua2c.lua clua \
	       $$DIR && \
	     cp examples-lua/*.lua $$DIR/examples-lua/ && \
	     cp lib/*.lua $$DIR/lib/ && \
	     cp lib/metalua/*.lua $$DIR/lib/metalua/ && \
	     tar czvf $$DIR.tar.gz $$DIR )

clean :
	rm -f *.stackdump
	rm -f `find . -name '*~'`
	rm -f `find . -name '*.c' -o -name '*.exe'`
	rm -fr lua2c-*
