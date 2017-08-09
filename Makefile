# project name (generate executable with this name)
TARGET   = bfss

export ABC_PATH = ${HOME}/Github/abc
export ABC_INCLUDES = -I$(ABC_PATH) -I$(ABC_PATH)/src

SRCDIR   = src
OBJDIR   = obj
BINDIR   = bin
LIBDIR   = lib


CC       = g++
# compiling flags here
CPP_FLAGS = -g -std=c++11 

# linking flags here
LFLAGS   = -g -std=c++11 $(LIBDIR)/libabc.a -lm -ldl -rdynamic -lreadline -ltermcap -lpthread -lrt -I $(ABC_INCLUDES)

SOURCES  := $(wildcard $(SRCDIR)/*.cpp)
INCLUDES := $(wildcard $(SRCDIR)/*.h)
OBJECTS  := $(SOURCES:$(SRCDIR)/%.cpp=$(OBJDIR)/%.o)
rm       = rm -f


$(BINDIR)/$(TARGET): $(OBJECTS)
	$(CC) $(CPP_FLAGS) -o $@ $^ $(LFLAGS) -I $(ABC_INCLUDES)
	@echo "Linking complete!"

$(OBJECTS): $(OBJDIR)/%.o : $(SRCDIR)/%.cpp
	$(CC) $(CPP_FLAGS) -c $^ -o $@ -I $(ABC_INCLUDES)
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

# %.o: %.cpp
# 	$(CC) $(CPP_FLAGS) -c $^ -o $@ -I $(ABC_INCLUDES)


# g++ -g -std=c++11  -c formula.cpp -o formula.o -I${HOME}/Github/abc -I${HOME}/Github/abc/src