CC ?= cc
CFLAGS ?= -O2 -g -Wall -Wextra -Wno-unused-parameter
SRC = core.c parser.c matcher.c engine.c main.c
OBJ = $(SRC:.c=.o)

reform: $(OBJ)
	$(CC) $(CFLAGS) -s -o $@ $(OBJ) -lm

%.o: %.c reform.h
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJ) reform

.PHONY: clean
