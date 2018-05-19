# project name (generate executable with this name)
BFSS 	= bfss
RCNF  	= readCnf

ABC_PATH = ./dependencies/abc
SCALMC_PATH = ./dependencies/scalmc

ifndef CXX
CXX = g++
endif

SRCDIR   = src
OBJDIR   = obj
BINDIR   = bin

TARGET_RCNF  = $(BINDIR)/$(RCNF)
TARGET_BFSS  = $(BINDIR)/$(BFSS)

ABC_INCLUDES = -I $(ABC_PATH) -I $(ABC_PATH)/src
UGEN_INCLUDES = -I $(SCALMC_PATH)/build/cmsat5-src/ -I $(SCALMC_PATH)/src/
LIB_DIRS = -L $(SCALMC_PATH)/build/lib/ -L $(ABC_PATH)/
DIR_INCLUDES = $(ABC_INCLUDES) $(UGEN_INCLUDES) $(LIB_DIRS)

LIB_UGEN   = -Wl,-Bdynamic -lcryptominisat5
LIB_ABC    = -Wl,-Bstatic  -labc
LIB_COMMON = -Wl,-Bdynamic -lm -ldl -lreadline -ltermcap -lpthread -fopenmp -lrt -Wl,-Bdynamic -lboost_program_options -Wl,-Bdynamic -lz

ifeq ($(UNIGEN), NO)
CPP_FLAGS = -g -std=c++11 -DNO_UNIGEN
LFLAGS    = $(DIR_INCLUDES) $(LIB_ABC) $(LIB_COMMON)
else
CPP_FLAGS = -g -std=c++11
LFLAGS    = $(DIR_INCLUDES) $(LIB_ABC) $(LIB_UGEN) $(LIB_COMMON)
endif

COMMON_SOURCES  = $(SRCDIR)/nnf.cpp $(SRCDIR)/helper.cpp

BFSS_SOURCES  = $(SRCDIR)/bfss.cpp $(COMMON_SOURCES)
BFSS_OBJECTS  = $(BFSS_SOURCES:$(SRCDIR)/%.cpp=$(OBJDIR)/%.o)
RCNF_SOURCES  = $(SRCDIR)/readCnf.cpp

.PHONY: all
all: $(TARGET_BFSS) $(TARGET_RCNF)

$(TARGET_BFSS): $(BFSS_OBJECTS)
	$(CXX) $(CPP_FLAGS) -o $@ $^ $(LFLAGS)
	@echo "Linking complete!"

$(TARGET_RCNF): $(RCNF_SOURCES)
	$(CXX) $(CPP_FLAGS) $^ -o $@
	@echo "Compiled "$^" successfully!"

$(BFSS_OBJECTS): $(OBJDIR)/%.o : $(SRCDIR)/%.cpp
	$(CXX) $(CPP_FLAGS) -c $^ -o $@  $(LFLAGS)
	@echo "Compiled "$<" successfully!"

.PHONY: clean
clean:
	@$(RM) $(BFSS_OBJECTS)
	@echo "Cleanup complete!"

.PHONY: remove
remove: clean
	@$(RM) $(TARGET_BFSS) $(TARGET_RCNF)
	@echo "Executable removed!"
