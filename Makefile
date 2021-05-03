.PHONY : all coq html website clean

all: coq

coq:
	$(MAKE) -C coq

clean:
	$(MAKE) -C coq clean
