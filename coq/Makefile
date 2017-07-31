METALIB = tlc
OTT = ott
PERL = perl
OTT_OPTS  = -tex_show_meta false
WARN_MSG = "%%% !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! %%%\n"
DOCKERIMAGE = ypyang/lamisub:coq-8.6.1

COQPREFIX =
INCLUDES = -R $(METALIB) TLC
COQFLAGS = -w -deprecated-implicit-arguments,-notation-overridden,-local-declaration
COQC = $(COQPREFIX)coqc $(INCLUDES) $(COQFLAGS)
COQDEP = $(COQPREFIX)coqdep $(INCLUDES)

src_ott = $(wildcard *.ott)
src_coq = $(wildcard *.v) $(src_ott:.ott=_ott.v)

src_tex = $(src_ott:.ott=.tex)
obj_ott = $(src_ott:.ott=.ott.tex)
obj_tex = $(src_tex:.tex=.gen)
obj_pdf := $(src_ott:.ott=.pdf)

dep_src = $(src_coq) $(wildcard $(METALIB)/*.v)

.PHONY: all latex clean distclean docker dockerbuild dockerclean
.SUFFIXES: .v .vo
.PRECIOUS: %.ott.tex %.gen

all: $(src_coq:.v=.vo)

latex: $(obj_pdf)

.v.vo : .depend
	@echo "Compiling $<"
	@$(COQC) $<

depend: .depend

.depend : $(dep_src) Makefile
	$(COQDEP) $(dep_src) > .depend

ifeq ($(findstring $(MAKECMDGOALS),depend clean distclean docker dockerbuild dockerclean),)
include .depend
endif

clean:
	rm -f *.vo .depend *.deps *.dot *.glob .*.aux .lia.cache $(obj_ott) $(obj_tex)

distclean: clean
	@rm -f $(METALIB)/*.vo $(METALIB)/*.glob $(METALIB)/*.v.d $(METALIB)/.*.aux || echo ok
	rm -Rf $(obj_pdf) .working *_ott.v
	rm -f *.gen

%.pdf: %.gen %.ott.tex otthelper.tex
	latexmk -pdf -outdir=.working -jobname=$(@:.pdf=) $<
	mv .working/$@ .

%_ott.v: %.ott
	$(OTT) -o $@ $<
	@$(PERL) -pi -e 's/^Require Import Metatheory/Require Import LibLN/' $@
	@$(PERL) -pi -e 's/^Definition x := var.//' $@
	@$(PERL) -pi -e 's/:x\)/:var\)/g' $@
	@$(PERL) -pi -e 's/: Set := LibEnv.env/:= LibEnv.env/g' $@
	@$(PERL) -pi -e 's/if \(k === nat\)/If (k = nat)/g' $@
	@$(PERL) -pi -e 's/=> \{}/=> \\{}/g' $@
	@$(PERL) -pi -e 's/=> \{\{(.*)}}/=> \\{$$1}/g' $@
	@$(PERL) -pi -e 's/if eq_var ([^\s]+)/If $$1 =/g' $@

%.ott.tex: %.ott
	$(OTT) -tex_wrap false $(OTT_OPTS) -o $@ $^
	@$(PERL) -0pi -e 's/\{%(\n|\r\n)\\ottpremise/{%\n/g' $@
	@$(PERL) -pi -e 's/^\\ottpremise/\\\\ /g' $@
	@$(PERL) -pi -e 's/^(.*\\ottlinebreak.*)$$/\\\\$$1/g' $@
	@$(PERL) -pi -e 's/\\Pi\s*\\,/\\Pi/g' $@

%.gen: %.tex %.ott
	$(OTT) $(OTT_OPTS) -tex_filter $< $@ $(word 2,$^)
	@$(PERL) -pi -e 'print $(WARN_MSG) if $$. == 1' $@
	@$(PERL) -pi -e 's/\\Pi\s*\\,/\\Pi/g' $@

docker:
	docker run -it --rm $(DOCKERIMAGE)

dockerbuild: Dockerfile
	docker build -t $(DOCKERIMAGE) .

dockerclean:
	docker rmi $(DOCKERIMAGE)

