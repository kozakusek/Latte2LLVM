.PHONY: all 

all: runtime exec

runtime: lib/runtime.c
	clang -S -emit-llvm -o lib/runtime.ll lib/runtime.c
	llvm-as lib/runtime.ll -o lib/runtime.bc

exec: src/*.hs src/Backend/*.hs src/Frontend/*.hs src/Latte.cf
	$(MAKE) -C src
	cp src/latc latc
	cp src/latc_llvm latc_llvm

clean:
	$(MAKE) -C src clean
	rm lib/runtime.ll
	rm lib/runtime.bc

distclean: clean
	$(MAKE) -C src distclean
	rm -f *.tar.gz
	rm -f latc
	rm -f latc_llvm

tar: distclean
	tar -czvf bk418339.tar.gz ./* 