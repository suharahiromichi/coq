OBJS = \
	Aw_0_Notations.vo \
	Aw_1_3_Categories.vo \
	Aw_1_4_Functors.vo \
	Aw_1_5_Isomorphisms.vo \
	Aw_1_6_1_ProductCategories.vo \
	Aw_1_6_2_OppositeCategories.vo \
	Aw_1_6_4_SliceCategories.vo \
	Aw_2_1_EpicMinic.vo \
	Aw_2_2_InitialTerminal.vo \
	Aw_7_4_NaturalTransformations.vo

all:	$(OBJS)

clean:;	rm -f *.vo *.glob

.SUFFIXES: .v .vo
.v.vo:
	coqc ${.IMPSRC}

# END
