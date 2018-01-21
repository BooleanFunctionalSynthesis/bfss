# project name (generate executable with this name)
TARGET   = bfss

ifndef ABC_PATH
export ABC_PATH = ${HOME}/abc
endif
ifndef SCALMC_PATH
export SCALMC_PATH = ${HOME}/Github/scalmcSampling
endif
ifndef BOOST_HOME
export BOOST_HOME = .
endif
ifndef CXX
export CXX = g++
endif

SRCDIR   = src
OBJDIR   = obj
BINDIR   = bin
LIBDIR   = lib

export ABC_INCLUDES = -I $(ABC_PATH) -I $(ABC_PATH)/src
export UGEN_INCLUDES = -I $(SCALMC_PATH)/build/cmsat5-src/ -I $(SCALMC_PATH)/src/
export BOOST_INCLUDES = -I $(BOOST_HOME)
export LIB_DIRS = -L $(LIBDIR)/ -L $(SCALMC_PATH)/build/lib/ -L $(BOOST_HOME)/stage/lib/
export DIR_INCLUDES = $(ABC_INCLUDES) $(UGEN_INCLUDES) $(BOOST_INCLUDES) $(LIB_DIRS)

export LIB_UNIGEN = -Wl,-Bdynamic -lcryptominisat5
export LIB_ABC = -Wl,-Bstatic -labc
export LIB_BOOST = -Wl,-Bdynamic -lboost_program_options

export CPP_FLAGS = -g -std=c++11

export LFLAGS   = $(DIR_INCLUDES) $(LIB_ABC) $(LIB_UNIGEN) -Wl,-Bdynamic -lm -ldl -lreadline -ltermcap -lpthread -fopenmp -lrt $(LIB_BOOST) -Wl,-Bdynamic -lm4ri  -Wl,-Bdynamic -lz



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
