SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g' | uniq
GREP_EXCLUDE = grep -v '^src/Comp2/\(SmallValues\|MediumValues\).v'

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
extocaml1:
	cd src/Comp1 && coqc Mem.v -R ../../src BY
ocaml1:
	mkdir -p bin && \
	cd src/Comp1 && \
	ocamlfind ocamlopt -O3 -linkpkg -package zarith -o ../../bin/comp1ocaml big.ml mem.mli mem.ml comp1.ml -rectypes
	# ocamlfind ocamlopt -O3 -c mem.mli mem.ml -rectypes && \
	# ocamlfind ocamlopt -O3 -c comp1.ml -rectypes && \
	# ocamlfind ocamlopt -O3 -o ../../bin/comp1ocaml mem.cmx comp1.cmx -rectypes
	# mkdir -p bin && \
	# cd src/Comp1 && \
	# ocamlfind ocamlopt -O3 -c comp1.mli comp1.ml -rectypes && \
	# ocamlfind ocamlopt -O3 -o ../../bin/comp1ocaml big.cmx mem.cmx comp1.cmx -rectypes

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
test-ocaml1:
	make ocaml1 && \
	time ./bin/comp1ocaml
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
update-makefile:
	git ls-files --deleted > deleted_files.tmp; \
	git ls-files 'src/*.v' > files.tmp; \
	if ! [ -s deleted_files.tmp ]; \
	then echo 'no deleted files' > deleted_files.tmp; \
	fi; \
	(echo 'INSTALLDEFAULTROOT = /' > _CoqProject); \
	(echo '-arg -w -arg -deprecated-instance-without-locality' >> _CoqProject); \
	(echo '-arg -w -arg +undeclared-scope' >> _CoqProject); \
	(echo '-Q src BY'; grep -vf deleted_files.tmp files.tmp | $(GREP_EXCLUDE) | $(SORT_COQPROJECT)) >> _CoqProject; \
	(echo '-Q coq-record-update RecordUpdate'; grep .v coq-record-update/_CoqProject | sed 's/^/coq-record-update\//') >> _CoqProject; \
	(echo '-Q stdpp stdpp'; grep .v stdpp/_CoqProject | sed 's/^/stdpp\//') >> _CoqProject; \
	rm *.tmp
	make coq-makefile
coq-makefile:
	coq_makefile -f _CoqProject -o CoqMakefile
