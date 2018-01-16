# project name (generate executable with this name)
TARGET   = bfss

ifndef ABC_PATH
export ABC_PATH = ${HOME}/abc
endif
export ABC_INCLUDES = -I$(ABC_PATH) -I$(ABC_PATH)/src
export LIB_UNIGEN = ~/Github/scalmcSampling/build/lib/libcryptominisat5.a -I/home/shubham/Github/scalmcSampling/build/cmsat5-src/ -I/home/shubham/Github/scalmcSampling/src/
export LIB_ABC = lib/libabc.a -I$(ABC_INCLUDES)

SRCDIR   = src
OBJDIR   = obj
BINDIR   = bin
LIBDIR   = lib


CC       = g++
# compiling flags here
CPP_FLAGS = -g -std=c++11

# linking flags here
LFLAGS   = $(LIB_ABC) $(LIB_UNIGEN) -lm -ldl -rdynamic -lreadline -ltermcap -lpthread -fopenmp -lrt -lboost_program_options -lz -lm4ri

SOURCES  := $(wildcard $(SRCDIR)/*.cpp)
INCLUDES := $(wildcard $(SRCDIR)/*.h)
SOURCES  := $(filter-out $(SRCDIR)/findDep.cpp, $(SOURCES))
INCLUDES := $(filter-out $(SRCDIR)/findDep.h,  $(INCLUDES))
OBJECTS  := $(SOURCES:$(SRCDIR)/%.cpp=$(OBJDIR)/%.o)
rm       = rm -f


$(BINDIR)/$(TARGET): $(OBJECTS)
	$(CC) $(CPP_FLAGS) -o $@ $^ $(LFLAGS)
	@echo "Linking complete!"

$(OBJECTS): $(OBJDIR)/%.o : $(SRCDIR)/%.cpp
	$(CC) $(CPP_FLAGS) -c $^ -o $@  $(LFLAGS)
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
