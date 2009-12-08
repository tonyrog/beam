
MODULES = \
	beam_load \
	beam_emu

EBIN = ../ebin
ERLC = erlc

include ../vsn.mk
VSN=$(BEAM_VSN)

APP_NAME= beam
APP_FILE= $(APP_NAME).app
APP_SRC= $(APP_FILE).src
APP_TARGET= $(EBIN)/$(APP_FILE)

ERL_FLAGS = \
	-I ../include -W0

override ERLC_FLAGS += $(ERL_FLAGS)

debug: ERLC_FLAGS += +debug_info -Ddebug -W

OBJS = $(MODULES:%=../ebin/%.beam) ../ebin/message.beam

TARGET_FILES = $(OBJS) $(APP_TARGET)

all: $(TARGET_FILES)

debug: all

depend:
	edep -MM -o ../ebin $(ERLC_FLAGS) $(MODULES:%=%.erl) > depend.mk

dialyze:
	dialyzer --src -o dia.out $(ERLC_FLAGS) -c $(MODULES:%=%.erl) 

edoc:
	erl -noshell -pa doc -run edoc_run application 'beam' '[{sort_functions,false},{todo,true},{index_columns,3}]'

clean:
	rm -f $(OBJS) 

$(APP_TARGET): $(APP_SRC) ../vsn.mk
	sed -e 's;%VSN%;$(VSN);'  $< > $@

-include depend.mk

../ebin/message.beam: message.S
	erlc -o ../ebin message.S

$(EBIN)/%.beam:	%.erl
	$(ERLC) $(ERLC_FLAGS) -o $(EBIN) $<

