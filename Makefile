all:
	make -f CoqMakefile
clean:
	make -f CoqMakefile clean
test-small:
	coqc src/Comp2/Comp2SmallValues.v -verbose -R src BY > smallvalues.log && \
	terminal-notifier -message 'Make test-small is done' -sound default
test-medium:
	coqc src/Comp2/Comp2MediumValues.v -verbose -R src BY > mediumvalues.log && \
	terminal-notifier -message 'Make test-medium is done' -sound default
ocaml:
	cd src/Comp2 && coqc Extraction.v -R ../../src BY && \
	ocamlfind ocamlopt -c definition.mli definition.ml -linkpkg -package coq.kernel -rectypes -thread && \
	ocamlfind ocamlopt -c comp2.ml  -linkpkg -package coq.kernel -rectypes -thread && \
	ocamlfind opt -o ../../bin/comp2ocaml definition.cmx comp2.cmx -linkpkg -package coq.kernel -rectypes -thread
c:
	gcc -O3 -o bin/comp2c src/Comp2/comp2.c
test-c:
	make c && \
	(time ./bin/comp2c 39 all) &> c.log && \
	terminal-notifier -message 'Make test-c is done' -sound default
test-ocaml:
	make ocaml && \
	(time ./bin/comp2ocaml 40 all) &> ocaml.log && \
	terminal-notifier -message 'Make test-ocaml is done' -sound default
