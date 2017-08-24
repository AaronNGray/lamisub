all:
	make -C coq

upload: oopsla17-extra.zip

appendix.pdf: paper-extended.pdf
	pdfjam $^ 27- -o $@

oopsla17-extra.zip: coq README.md appendix.pdf
	make -C coq distclean
	git checkout coq
	mv README.md README.md.bak
	sed 's/paper-extended/appendix/g' README.md.bak > README.md
	zip -r -X $@ $^ -x "*.DS_Store"
	mv README.md.bak README.md

clean:
	make -C coq clean
	rm -f oopsla17-extra.zip appendix.pdf

.PHONY: clean all upload
