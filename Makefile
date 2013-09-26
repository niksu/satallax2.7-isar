# OCAMLARGS = -g  # Uncomment if debugging
CXX       ?= g++

COQC = coqc

all : opt bytecode

bytecode : bin/satallax

opt : bin/satallax.opt

bin/satallax : bin/tptp_lexer.cmo bin/formula.cmo bin/tptp_config.cmo bin/tptp_parser.cmo bin/proofterm.cmo bin/search.cmo bin/syntax.cmo bin/state.cmo bin/coqlexer.cmo bin/coqparser.cmo bin/flags.cmo bin/match.cmo bin/version.cmo bin/config.cmo bin/satallaxmain.cmo bin/satallax.cmo bin/minisatinterface.cmo bin/dllminisatinterface.so
	ocamlc $(OCAMLARGS) -I bin -o bin/satallax unix.cma $(PWD)/bin/dllminisatinterface.so bin/minisatinterface.cmo bin/syntax.cmo bin/config.cmo bin/flags.cmo bin/match.cmo bin/priorityqueue.cmo bin/state.cmo bin/search.cmo bin/refutation.cmo bin/flag.cmo bin/litcount.cmo bin/branch.cmo bin/step.cmo bin/suche.cmo bin/translation.cmo bin/coq.cmo bin/latex.cmo bin/proofterm.cmo bin/coqlexer.cmo bin/coqparser.cmo bin/tptp_lexer.cmo bin/formula.cmo bin/tptp_config.cmo bin/tptp_parser.cmo bin/version.cmo bin/satallaxmain.cmo bin/satallax.cmo

bin/satallax.opt : bin/tptp_lexer.cmx bin/formula.cmx bin/tptp_config.cmx bin/tptp_parser.cmx bin/proofterm.cmx bin/search.cmx bin/syntax.cmx bin/state.cmx bin/coqlexer.cmx bin/coqparser.cmx bin/flags.cmx bin/match.cmx bin/version.cmx bin/config.cmx bin/satallaxmain.cmx bin/satallax.cmx bin/minisatinterface.cmx bin/libminisatinterface.a bin/priorityqueue.cmx
	ocamlopt -I bin -o bin/satallax.opt $(PWD)/bin/libminisatinterface.a unix.cmxa bin/minisatinterface.cmx bin/syntax.cmx bin/config.cmx bin/flags.cmx bin/match.cmx bin/priorityqueue.cmx bin/state.cmx bin/search.cmx bin/refutation.cmx bin/flag.cmx bin/litcount.cmx bin/branch.cmx bin/step.cmx bin/suche.cmx bin/translation.cmx bin/coq.cmx bin/latex.cmx bin/proofterm.cmx bin/coqlexer.cmx bin/coqparser.cmx bin/tptp_lexer.cmx bin/formula.cmx bin/tptp_config.cmx bin/tptp_parser.cmx bin/version.cmx bin/satallaxmain.cmx bin/satallax.cmx -cclib -lstdc++

bin/satallaxcoqtac : bin/satallaxcoqtac.cmx bin/satallaxmain.cmx
	ocamlopt -I bin -o bin/satallaxcoqtac $(PWD)/bin/libminisatinterface.a unix.cmxa bin/minisatinterface.cmx bin/syntax.cmx bin/config.cmx bin/flags.cmx bin/match.cmx bin/priorityqueue.cmx bin/state.cmx bin/search.cmx bin/refutation.cmx bin/flag.cmx bin/litcount.cmx bin/branch.cmx bin/step.cmx bin/suche.cmx bin/translation.cmx bin/coq.cmx bin/latex.cmx bin/proofterm.cmx bin/tptp_lexer.cmx bin/formula.cmx bin/tptp_config.cmx bin/tptp_parser.cmx bin/version.cmx bin/satallaxmain.cmx bin/satallaxcoqtac.cmx -cclib -lstdc++

bin/satallax.cmo : src/satallax.ml bin/satallaxmain.cmi  bin/satallaxmain.cmo bin/coqparser.cmo bin/search.cmo bin/syntax.cmo bin/state.cmo bin/flags.cmo bin/coqparser.cmo
	ocamlc $(OCAMLARGS) -I bin -o bin/satallax.cmo -c src/satallax.ml

bin/satallax.cmx : src/satallax.ml bin/satallaxmain.cmi bin/satallaxmain.cmx bin/coqparser.cmx bin/search.cmx bin/syntax.cmx bin/state.cmx bin/flags.cmx bin/coqparser.cmx
	ocamlopt -I bin -o bin/satallax.cmx -c src/satallax.ml

bin/satallaxmain.cmi : src/satallaxmain.mli bin/proofterm.cmi bin/search.cmi bin/syntax.cmi bin/state.cmi bin/flags.cmi bin/coqparser.cmi
	ocamlc $(OCAMLARGS) -I bin -o bin/satallaxmain.cmi -c src/satallaxmain.mli

bin/satallaxmain.cmo : src/satallaxmain.ml bin/satallaxmain.cmi bin/proofterm.cmo bin/search.cmo bin/syntax.cmo bin/state.cmo bin/flags.cmo
	ocamlc $(OCAMLARGS) -I bin -o bin/satallaxmain.cmo -c src/satallaxmain.ml

bin/satallaxmain.cmx : src/satallaxmain.ml bin/satallaxmain.cmi bin/proofterm.cmx bin/search.cmx bin/syntax.cmx bin/state.cmx bin/flags.cmx
	ocamlopt -I bin -o bin/satallaxmain.cmx -c src/satallaxmain.ml

bin/satallaxcoqtac.cmx : src/satallaxcoqtac.ml bin/satallax.cmx
	ocamlopt $(OCAMLARGS) -I bin -o bin/satallaxcoqtac.cmx -c src/satallaxcoqtac.ml

bin/minisatinterface.cmo : src/minisatinterface.ml
	ocamlc $(OCAMLARGS) -I bin -o bin/minisatinterface.cmo -c src/minisatinterface.ml

bin/minisatinterface.cmx : src/minisatinterface.ml
	ocamlopt -I bin -o bin/minisatinterface.cmx -c src/minisatinterface.ml

bin/dllminisatinterface.so : bin/minisatinterface.cmo bin/Ointerface.o
	ocamlmklib -o bin/minisatinterface minisat/core/Solver.o minisat/simp/SimpSolver.o bin/Ointerface.o -lstdc++

bin/libminisatinterface.a : bin/minisatinterface.cmo bin/Ointerface.o
	ocamlmklib -o bin/minisatinterface minisat/core/Solver.o minisat/simp/SimpSolver.o bin/Ointerface.o -lstdc++

bin/Ointerface.o : src/minisat-interface/Ointerface.cc
	$(CXX) -c -fPIC -Wall -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -Iminisat -I"`ocamlc -where`" -o bin/Ointerface.o src/minisat-interface/Ointerface.cc

bin/version.cmo : src/version.ml bin/version.cmi
	ocamlc $(OCAMLARGS) -I bin -o bin/version.cmo -c src/version.ml

bin/version.cmx : src/version.ml bin/version.cmi
	ocamlopt -I bin -o bin/version.cmx -c src/version.ml

bin/version.cmi : src/version.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/version.cmi -c src/version.mli

bin/config.cmo : src/config.ml bin/config.cmi
	ocamlc $(OCAMLARGS) -I bin -o bin/config.cmo -c src/config.ml

bin/config.cmx : src/config.ml bin/config.cmi
	ocamlopt -I bin -o bin/config.cmx -c src/config.ml

bin/config.cmi : src/config.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/config.cmi -c src/config.mli

bin/flags.cmo : src/flags.ml bin/flags.cmi
	ocamlc $(OCAMLARGS) -I bin -o bin/flags.cmo -c src/flags.ml

bin/flags.cmx : src/flags.ml bin/flags.cmi
	ocamlopt -I bin -o bin/flags.cmx -c src/flags.ml

bin/flags.cmi : src/flags.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/flags.cmi -c src/flags.mli

bin/priorityqueue.cmi : src/priorityqueue.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/priorityqueue.cmi -c src/priorityqueue.mli

bin/priorityqueue.cmo : src/priorityqueue.ml
	ocamlc $(OCAMLARGS) -I bin -o bin/priorityqueue.cmo -c src/priorityqueue.ml

bin/priorityqueue.cmx : src/priorityqueue.ml
	ocamlopt -I bin -o bin/priorityqueue.cmx -c src/priorityqueue.ml

bin/state.cmi : bin/syntax.cmi src/state.mli bin/syntax.cmi bin/config.cmi bin/priorityqueue.cmi
	ocamlc $(OCAMLARGS) -I bin -o bin/state.cmi -c src/state.mli

bin/state.cmo : src/state.ml bin/state.cmi bin/flags.cmo bin/syntax.cmo bin/tptp_lexer.cmo bin/tptp_parser.cmi bin/config.cmi bin/priorityqueue.cmo bin/minisatinterface.cmo
	ocamlc $(OCAMLARGS) -I bin -o bin/state.cmo -c src/state.ml

bin/state.cmx : src/state.ml bin/state.cmi bin/flags.cmx bin/syntax.cmx bin/tptp_lexer.cmo bin/tptp_parser.cmi bin/config.cmi bin/priorityqueue.cmx bin/minisatinterface.cmx
	ocamlopt -I bin -o bin/state.cmx -c src/state.ml

bin/syntax.cmi : src/syntax.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/syntax.cmi -c src/syntax.mli

bin/syntax.cmo : src/syntax.ml bin/syntax.cmi
	ocamlc $(OCAMLARGS) -I bin -o bin/syntax.cmo -c src/syntax.ml

bin/syntax.cmx : src/syntax.ml bin/syntax.cmi
	ocamlopt -I bin -o bin/syntax.cmx -c src/syntax.ml

bin/search.cmi : src/search.mli bin/flags.cmi bin/state.cmi bin/config.cmi bin/match.cmi
	ocamlc $(OCAMLARGS) -I bin -o bin/search.cmi -c src/search.mli

bin/search.cmo : src/search.ml bin/search.cmi bin/flags.cmo bin/state.cmo bin/config.cmo bin/minisatinterface.cmo bin/match.cmo
	ocamlc $(OCAMLARGS) -I bin -o bin/search.cmo -c src/search.ml

bin/search.cmx : src/search.ml bin/search.cmi bin/flags.cmx bin/state.cmx bin/config.cmx bin/match.cmx bin/minisatinterface.cmx
	ocamlopt -I bin -o bin/search.cmx -c src/search.ml
 

bin/branch.cmi: bin/state.cmi src/pfterm/branch.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/branch.cmi -c src/pfterm/branch.mli

bin/coq.cmi: bin/refutation.cmi src/pfterm/coq.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/coq.cmi -c src/pfterm/coq.mli

bin/flag.cmi: src/pfterm/flag.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/flag.cmi -c src/pfterm/flag.mli

bin/latex.cmi: bin/state.cmi bin/refutation.cmi src/pfterm/latex.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/latex.cmi -c src/pfterm/latex.mli

bin/litcount.cmi: src/pfterm/litcount.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/litcount.cmi -c src/pfterm/litcount.mli

bin/proofterm.cmi: bin/state.cmi src/pfterm/proofterm.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/proofterm.cmi -c src/pfterm/proofterm.mli

bin/refutation.cmi: bin/syntax.cmi src/pfterm/refutation.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/refutation.cmi -c src/pfterm/refutation.mli

bin/step.cmi: bin/litcount.cmi bin/branch.cmi src/pfterm/step.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/step.cmi -c src/pfterm/step.mli

bin/suche.cmi: bin/refutation.cmi bin/branch.cmi bin/state.cmi src/pfterm/suche.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/suche.cmi -c src/pfterm/suche.mli

bin/translation.cmi: bin/refutation.cmi src/pfterm/translation.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/translation.cmi -c src/pfterm/translation.mli

bin/branch.cmo: bin/refutation.cmo bin/flag.cmo bin/state.cmo bin/branch.cmi src/pfterm/branch.ml
	ocamlc $(OCAMLARGS) -I bin -o bin/branch.cmo -c src/pfterm/branch.ml

bin/branch.cmx: bin/refutation.cmx bin/flag.cmx bin/state.cmx bin/branch.cmi src/pfterm/branch.ml
	ocamlopt -I bin -o bin/branch.cmx -c src/pfterm/branch.ml

bin/coq.cmo: bin/refutation.cmo bin/flag.cmo src/pfterm/coq.ml bin/coq.cmi 
	ocamlc $(OCAMLARGS) -I bin -o bin/coq.cmo -c src/pfterm/coq.ml

bin/coq.cmx: bin/refutation.cmx bin/flag.cmx src/pfterm/coq.ml bin/coq.cmi 
	ocamlopt -I bin -o bin/coq.cmx -c src/pfterm/coq.ml

bin/flag.cmo: bin/flag.cmi src/pfterm/flag.ml
	ocamlc $(OCAMLARGS) -I bin -o bin/flag.cmo -c src/pfterm/flag.ml

bin/flag.cmx: bin/flag.cmi src/pfterm/flag.ml
	ocamlopt -I bin -o bin/flag.cmx -c src/pfterm/flag.ml

bin/latex.cmo: bin/state.cmo bin/refutation.cmo bin/latex.cmi src/pfterm/latex.ml
	ocamlc $(OCAMLARGS) -I bin -o bin/latex.cmo -c src/pfterm/latex.ml

bin/latex.cmx: bin/state.cmx bin/refutation.cmx bin/latex.cmi src/pfterm/latex.ml
	ocamlopt -I bin -o bin/latex.cmx -c src/pfterm/latex.ml

bin/litcount.cmo: bin/flag.cmo src/pfterm/litcount.ml bin/litcount.cmi 
	ocamlc $(OCAMLARGS) -I bin -o bin/litcount.cmo -c src/pfterm/litcount.ml

bin/litcount.cmx: bin/flag.cmx src/pfterm/litcount.ml bin/litcount.cmi 
	ocamlopt -I bin -o bin/litcount.cmx -c src/pfterm/litcount.ml

bin/proofterm.cmo: bin/search.cmo bin/translation.cmo bin/suche.cmo bin/refutation.cmo bin/latex.cmo \
    bin/flag.cmo bin/coq.cmo bin/branch.cmo src/pfterm/proofterm.ml bin/proofterm.cmi
	ocamlc $(OCAMLARGS) -I bin -o bin/proofterm.cmo -c src/pfterm/proofterm.ml

bin/proofterm.cmx: bin/search.cmx bin/translation.cmx bin/suche.cmx bin/refutation.cmx bin/latex.cmx \
    bin/flag.cmx bin/coq.cmx bin/branch.cmx src/pfterm/proofterm.ml bin/proofterm.cmi 
	ocamlopt -I bin -o bin/proofterm.cmx -c src/pfterm/proofterm.ml

bin/refutation.cmo: bin/refutation.cmi src/pfterm/refutation.ml
	ocamlc $(OCAMLARGS) -I bin -o bin/refutation.cmo -c src/pfterm/refutation.ml

bin/refutation.cmx: bin/refutation.cmi src/pfterm/refutation.ml
	ocamlopt -I bin -o bin/refutation.cmx -c src/pfterm/refutation.ml

bin/step.cmo: bin/litcount.cmo bin/flag.cmo bin/branch.cmo src/pfterm/step.ml bin/step.cmi 
	ocamlc $(OCAMLARGS) -I bin -o bin/step.cmo -c src/pfterm/step.ml

bin/step.cmx: bin/litcount.cmx bin/flag.cmx bin/branch.cmx src/pfterm/step.ml bin/step.cmi 
	ocamlopt -I bin -o bin/step.cmx -c src/pfterm/step.ml

bin/suche.cmo: bin/step.cmo bin/refutation.cmo bin/litcount.cmo bin/flag.cmo bin/branch.cmo src/pfterm/suche.ml bin/suche.cmi 
	ocamlc $(OCAMLARGS) -I bin -o bin/suche.cmo -c src/pfterm/suche.ml

bin/suche.cmx: bin/step.cmx bin/refutation.cmx bin/litcount.cmx bin/flag.cmx bin/branch.cmx src/pfterm/suche.ml bin/suche.cmi 
	ocamlopt -I bin -o bin/suche.cmx -c src/pfterm/suche.ml

bin/translation.cmo: bin/refutation.cmo bin/flag.cmo src/pfterm/translation.ml bin/translation.cmi 
	ocamlc $(OCAMLARGS) -I bin -o bin/translation.cmo -c src/pfterm/translation.ml

bin/translation.cmx: bin/refutation.cmx bin/flag.cmx src/pfterm/translation.ml bin/translation.cmi 
	ocamlopt -I bin -o bin/translation.cmx -c src/pfterm/translation.ml


bin/formula.cmi : src/parser/formula.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/formula.cmi -c src/parser/formula.mli

bin/formula.cmo : src/parser/formula.ml bin/formula.cmi
	ocamlc $(OCAMLARGS) -I bin -o bin/formula.cmo -c src/parser/formula.ml

bin/formula.cmx : src/parser/formula.ml bin/formula.cmi
	ocamlopt -I bin -o bin/formula.cmx -c src/parser/formula.ml

bin/match.cmi : src/match.mli bin/syntax.cmi bin/state.cmi
	ocamlc $(OCAMLARGS) -I bin -o bin/match.cmi -c src/match.mli

bin/match.cmo : src/match.ml bin/match.cmi bin/syntax.cmo bin/state.cmo
	ocamlc $(OCAMLARGS) -I bin -o bin/match.cmo -c src/match.ml

bin/match.cmx : src/match.ml bin/match.cmi bin/syntax.cmx bin/state.cmx
	ocamlopt -I bin -o bin/match.cmx -c src/match.ml

bin/tptp_config.cmi : src/parser/tptp_config.mli
	ocamlc $(OCAMLARGS) -I bin -o bin/tptp_config.cmi -c src/parser/tptp_config.mli

bin/tptp_config.cmo : src/parser/tptp_config.ml bin/tptp_config.cmi bin/syntax.cmo bin/state.cmo
	ocamlc $(OCAMLARGS) -I bin -o bin/tptp_config.cmo -c src/parser/tptp_config.ml

bin/tptp_config.cmx : src/parser/tptp_config.ml bin/tptp_config.cmi bin/syntax.cmx bin/state.cmx 
	ocamlopt -I bin -o bin/tptp_config.cmx -c src/parser/tptp_config.ml

bin/tptp_lexer.cmo : src/parser/tptp_lexer.ml bin/tptp_parser.cmi
	ocamlc $(OCAMLARGS) -I bin -o bin/tptp_lexer.cmo -c src/parser/tptp_lexer.ml

bin/tptp_lexer.cmx : src/parser/tptp_lexer.ml bin/tptp_parser.cmi
	ocamlopt -I bin -o bin/tptp_lexer.cmx -c src/parser/tptp_lexer.ml

src/parser/tptp_lexer.ml : src/parser/tptp_lexer.mll bin/tptp_parser.cmi
	ocamllex src/parser/tptp_lexer.mll

bin/tptp_parser.cmi : src/parser/tptp_parser.mli bin/syntax.cmi bin/state.cmi bin/formula.cmi bin/tptp_config.cmi
	ocamlc $(OCAMLARGS) -I bin -o bin/tptp_parser.cmi -c src/parser/tptp_parser.mli

bin/tptp_parser.cmo : bin/tptp_parser.cmi src/parser/tptp_parser.ml bin/formula.cmo bin/tptp_config.cmo
	ocamlc $(OCAMLARGS) -I bin -o bin/tptp_parser.cmo -c src/parser/tptp_parser.ml

bin/tptp_parser.cmx : bin/tptp_parser.cmi src/parser/tptp_parser.ml bin/formula.cmx bin/tptp_config.cmx
	ocamlopt -I bin -o bin/tptp_parser.cmx -c src/parser/tptp_parser.ml

src/parser/tptp_parser.ml : src/parser/tptp_parser.mly
	ocamlyacc src/parser/tptp_parser.mly

src/parser/tptp_parser.mli : src/parser/tptp_parser.mly
	ocamlyacc src/parser/tptp_parser.mly

bin/coqlexer.cmo : src/coqparser/coqlexer.ml bin/coqparser.cmi
	ocamlc $(OCAMLARGS) -I bin -o bin/coqlexer.cmo -c src/coqparser/coqlexer.ml

bin/coqlexer.cmx : src/coqparser/coqlexer.ml bin/coqparser.cmi
	ocamlopt -I bin -o bin/coqlexer.cmx -c src/coqparser/coqlexer.ml

bin/coqparser.cmi : src/coqparser/coqparser.mli bin/syntax.cmi bin/state.cmi
	ocamlc $(OCAMLARGS) -I bin -o bin/coqparser.cmi -c src/coqparser/coqparser.mli

bin/coqparser.cmo : bin/coqparser.cmi bin/state.cmo src/coqparser/coqparser.ml
	ocamlc $(OCAMLARGS) -I bin -o bin/coqparser.cmo -c src/coqparser/coqparser.ml

bin/coqparser.cmx : bin/coqparser.cmi bin/state.cmx src/coqparser/coqparser.ml
	ocamlopt -I bin -o bin/coqparser.cmx -c src/coqparser/coqparser.ml

src/coqparser/coqlexer.ml : src/coqparser/coqlexer.mll bin/coqparser.cmi
	ocamllex src/coqparser/coqlexer.mll

src/coqparser/coqparser.ml : src/coqparser/coqparser.mly
	ocamlyacc src/coqparser/coqparser.mly

src/coqparser/coqparser.mli : src/coqparser/coqparser.mly
	ocamlyacc src/coqparser/coqparser.mly

coq :  coq/stttab.vo coq2/set0a.vo

coq/stttab.vo : coq/stt.vo coq/stttab.v
	cd coq; $(COQC) stttab

coq/stt.vo : coq/stt.v
	cd coq; $(COQC) stt

coq2/stt0.vo : coq2/stt0.v
	cd coq2; $(COQC) -nois stt0

coq2/stt1.vo : coq2/stt1.v coq2/stt0.vo
	cd coq2; $(COQC) -nois stt1

coq2/stt2.vo : coq2/stt2.v coq2/stt1.vo
	cd coq2; $(COQC) -nois stt2

coq2/stt3.vo : coq2/stt3.v coq2/stt2.vo
	cd coq2; $(COQC) -nois stt3

coq2/stt4.vo : coq2/stt4.v coq2/stt3.vo
	cd coq2; $(COQC) -nois stt4

coq2/set0a.vo : coq2/set0a.v coq2/stt4.vo
	cd coq2; $(COQC) -nois set0a

clean :
	rm bin/*.cma bin/*.o bin/*.opt bin/*.so bin/*.a bin/*.cmo bin/*.cmi bin/*.cmx src/parser/tptp_parser.ml src/parser/tptp_parser.mli src/parser/tptp_lexer.ml src/coqparser/coqparser.ml src/coqparser/coqparser.mli src/coqparser/coqlexer.ml bin/satallax bin/satallax.opt

