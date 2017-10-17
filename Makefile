# project name (generate executable with this name)
TARGET   = bfss

ifndef ABC_PATH
export ABC_PATH = ${HOME}/abc
endif
export ABC_INCLUDES = -I$(ABC_PATH) -I$(ABC_PATH)/src
export LIB_UNIGEN = /usr/local/lib/libunigen.a
export LIB_ABC = lib/libabc.a

SRCDIR   = src
OBJDIR   = obj
BINDIR   = bin
LIBDIR   = lib


CC       = g++
# compiling flags here
CPP_FLAGS = -g -std=c++11

# linking flags here
LFLAGS   = -g -std=c++11 $(LIB_ABC) $(LIB_UNIGEN) -lm -ldl -rdynamic -lreadline -ltermcap -lpthread -fopenmp -lrt $(ABC_INCLUDES)

SOURCES  := $(wildcard $(SRCDIR)/*.cpp)
INCLUDES := $(wildcard $(SRCDIR)/*.h)
SOURCES  := $(filter-out $(SRCDIR)/bfss_old.cpp, $(SOURCES))
INCLUDES := $(filter-out $(SRCDIR)/bfss_old.h,  $(INCLUDES))
OBJECTS  := $(SOURCES:$(SRCDIR)/%.cpp=$(OBJDIR)/%.o)
rm       = rm -f


$(BINDIR)/$(TARGET): $(OBJECTS)
	$(CC) $(CPP_FLAGS) -o $@ $^ $(LFLAGS) $(ABC_INCLUDES)
	@echo "Linking complete!"

$(OBJECTS): $(OBJDIR)/%.o : $(SRCDIR)/%.cpp
	$(CC) $(CPP_FLAGS) -c $^ -o $@ $(ABC_INCLUDES)
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
