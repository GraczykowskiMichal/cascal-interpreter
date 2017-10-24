.PHONY:	all	install	clean

all: install

install:
		@echo "Building Cascal interpreter..."
		@ghc --make interpreter.hs
		@echo "Building finished successfully."

clean:
		@echo "Deleting binaries and linker files..."
		-@rm *.hi
		-@rm *.o
		-@rm interpreter
		@echo "Deleting finished successfully."