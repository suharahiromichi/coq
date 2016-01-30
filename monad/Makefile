OBJS = \
	Notations.vo \
	Categories.vo \
	Functors.vo \
	Isomorphisms.vo \
	OppositeCategories.vo \
	ProductCategories.vo \
	SliceCategories.vo


all:	$(OBJS)

clean:;	rm -f *.vo *.glob

.SUFFIXES: .v .vo
.v.vo:
	coqc ${.IMPSRC}

# END
