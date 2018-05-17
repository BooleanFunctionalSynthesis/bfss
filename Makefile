# project name (generate executable with this name)
TARGET   = bfss

ABC_PATH = ./dependencies/abc
SCALMC_PATH = ./dependencies/scalmc

ifndef CXX
export CXX = g++
endif

SRCDIR   = src
OBJDIR   = obj
BINDIR   = bin

export ABC_INCLUDES = -I $(ABC_PATH) -I $(ABC_PATH)/src
export UGEN_INCLUDES = -I $(SCALMC_PATH)/build/cmsat5-src/ -I $(SCALMC_PATH)/src/
export LIB_DIRS = -L $(SCALMC_PATH)/build/lib/ -L $(ABC_PATH)/
export DIR_INCLUDES = $(ABC_INCLUDES) $(UGEN_INCLUDES) $(LIB_DIRS)

export LIB_UGEN  = -Wl,-Bdynamic -lcryptominisat5
export LIB_ABC   = -Wl,-Bstatic  -labc
export LIB_BOOST = -Wl,-Bdynamic -lboost_program_options

ifeq ($(UNIGEN), NO)
export CPP_FLAGS = -g -std=c++11 -DNO_UNIGEN
export LFLAGS   = $(DIR_INCLUDES) $(LIB_ABC) -Wl,-Bdynamic -lm -ldl -lreadline -ltermcap -lpthread -fopenmp -lrt $(LIB_BOOST) -Wl,-Bdynamic -lz
else
export CPP_FLAGS = -g -std=c++11
export LFLAGS   = $(DIR_INCLUDES) $(LIB_ABC) $(LIB_UGEN) -Wl,-Bdynamic -lm -ldl -lreadline -ltermcap -lpthread -fopenmp -lrt $(LIB_BOOST) -Wl,-Bdynamic -lz
endif


SOURCES  := $(wildcard $(SRCDIR)/*.cpp)
INCLUDES := $(wildcard $(SRCDIR)/*.h)
SOURCES  := $(filter-out $(SRCDIR)/findDep.cpp, $(SOURCES))
INCLUDES := $(filter-out $(SRCDIR)/findDep.h,  $(INCLUDES))
OBJECTS  := $(SOURCES:$(SRCDIR)/%.cpp=$(OBJDIR)/%.o)
rm       = rm -f


$(BINDIR)/$(TARGET): $(OBJECTS)
	$(CXX) $(CPP_FLAGS) -o $@ $^ $(LFLAGS)
	@echo "Linking complete!"

$(OBJECTS): $(OBJDIR)/%.o : $(SRCDIR)/%.cpp
	$(CXX) $(CPP_FLAGS) -c $^ -o $@  $(LFLAGS)
	@echo "Compiled "$<" successfully!"

.PHONY: all
all: $(TARGET)

.PHONY: clean
clean:
	@$(rm) $(OBJECTS)
	@echo "Cleanup complete!"

.PHONY: remove
remove: clean
	@$(rm) $(BINDIR)/$(TARGET)
	@echo "Executable removed!"
