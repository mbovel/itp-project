SRCS=Equivalence.vo DisjointSet.vo

all: ${SRCS}

%.vo: %.v
	coqc $<

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux
