SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g' | uniq

all:
	make -f CoqMakefile
clean:
	make -f CoqMakefile clean
test-small:
	coqc src/Comp2/SmallValues.v -verbose -R src BY > smallvalues.log && \
	terminal-notifier -message 'Make test-small is done' -sound default
test-medium:
	coqc src/Comp2/MediumValues.v -verbose -R src BY > mediumvalues.log && \
	terminal-notifier -message 'Make test-medium is done' -sound default
ocaml:
	mkdir -p bin && \
	cd src/Comp2 && coqc Extraction.v -R ../../src BY && \
	ocamlfind ocamlopt -O3 -c definition.mli definition.ml -linkpkg -package coq.kernel -rectypes -thread && \
	ocamlfind ocamlopt -O3 -c table.mli table.ml -linkpkg -package coq.kernel -rectypes -thread && \
	ocamlfind ocamlopt -O3 -c comp2.ml  -linkpkg -package coq.kernel -rectypes -thread && \
	ocamlfind ocamlopt -O3 -o ../../bin/comp2ocaml definition.cmx comp2.cmx -linkpkg -package coq.kernel -rectypes -thread
c:
	mkdir -p bin && \
	gcc -O3 -o bin/comp2c src/Comp2/comp2.c
c-no-opt:
	mkdir -p bin && \
	gcc -o bin/comp2c src/Comp2/comp2.c
test-c:
	mkdir -p bin && \
	make c && \
	(time ./bin/comp2c 39 all) &> c.log && \
	terminal-notifier -message 'Make test-c is done' -sound default
test-c-2:
	mkdir -p bin && \
	make c && \
	(time ./bin/comp2c 39 all) && \
	terminal-notifier -message 'Make test-c is done' -sound default
test-ocaml:
	mkdir -p bin && \
	make ocaml && \
	(time ./bin/comp2ocaml 40 all) &> ocaml.log && \
	terminal-notifier -message 'Make test-ocaml is done' -sound default
test-ocaml-2:
	mkdir -p bin && \
	make ocaml && \
	(time ./bin/comp2ocaml 50 all) && \
	terminal-notifier -message 'Make test-ocaml is done' -sound default
update-_CoqProject:
	(echo '-R src BY'; (git ls-files 'src/*.v' | grep -v '^src/Comp2/\(SmallValues\|MediumValues\).v' | $(SORT_COQPROJECT))) > _CoqProject
