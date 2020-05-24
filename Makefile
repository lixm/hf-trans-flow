
default: all

all: LibTactics.v SfLib.v Entities.v TransFlow.v Example.v Safety.v
	coqc LibTactics.v
	coqc SfLib.v
	coqc MyUtils.v
	coqc Entities.v
	coqc TransFlow.v
	coqc Example.v
	coqc Safety.v

clean:
	rm *.vo
	rm *.glob
	rm .*aux
	rm .lia.cache
