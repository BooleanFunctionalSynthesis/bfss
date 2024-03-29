# optional arguments:
# 	UNIGEN=NO
# 	BUILD=RELEASE/DEBUG

# Architecture required by ABC
CPP_FLAGS += -DLIN64

BFSS 	= bfss
RCNF  	= readCnf
ORDR  	= genVarOrder
VRFY  	= verify
RSUB    = revsub

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
TARGET_ORDR  = $(BINDIR)/$(ORDR)
TARGET_VRFY  = $(BINDIR)/$(VRFY)
TARGET_RSUB  = $(BINDIR)/$(RSUB)

ABC_INCLUDES = -I $(ABC_PATH) -I $(ABC_PATH)/src
UGEN_INCLUDES = -I $(SCALMC_PATH)/build/cmsat5-src/ -I $(SCALMC_PATH)/src/
LIB_DIRS = -L $(SCALMC_PATH)/build/lib/ -L $(ABC_PATH)/
DIR_INCLUDES = $(ABC_INCLUDES) $(UGEN_INCLUDES) $(LIB_DIRS)

LIB_UGEN   = -Wl,-Bdynamic -lcryptominisat5
LIB_ABC    = -Wl,-Bstatic  -labc
LIB_COMMON = -Wl,-Bdynamic -lm -ldl -lreadline -ltermcap -lpthread -fopenmp -lrt -Wl,-Bdynamic -lboost_program_options -Wl,-Bdynamic -lz

ifeq ($(UNIGEN), NO)
CPP_FLAGS += -std=c++11 -DNO_UNIGEN
LFLAGS    = $(DIR_INCLUDES) $(LIB_ABC) $(LIB_COMMON)
else
CPP_FLAGS += -std=c++11
LFLAGS    = $(DIR_INCLUDES) $(LIB_ABC) $(LIB_UGEN) $(LIB_COMMON)
endif

ifeq ($(BUILD),DEBUG)
CPP_FLAGS += -O0 -g
else ifeq ($(BUILD),RELEASE)
CPP_FLAGS += -O3 -s -DNDEBUG
else
CPP_FLAGS += -O3
endif

COMMON_SOURCES  = $(SRCDIR)/nnf.cpp $(SRCDIR)/helper.cpp

BFSS_SOURCES  = $(SRCDIR)/bfss.cpp $(COMMON_SOURCES)
ORDR_SOURCES  = $(SRCDIR)/genVarOrder.cpp $(COMMON_SOURCES)
RCNF_SOURCES  = $(SRCDIR)/readCnf.cpp
VRFY_SOURCES  = $(SRCDIR)/verify.cpp
RSUB_SOURCES  = $(SRCDIR)/revsub.cpp
BFSS_OBJECTS  = $(BFSS_SOURCES:$(SRCDIR)/%.cpp=$(OBJDIR)/%.o)
ORDR_OBJECTS  = $(ORDR_SOURCES:$(SRCDIR)/%.cpp=$(OBJDIR)/%.o)
ALL_OBJECTS   = $(sort $(BFSS_OBJECTS) $(ORDR_OBJECTS))

.PHONY: all clean remove bfss readCnf genVarOrder verify revsub directories
all: bfss readCnf genVarOrder verify revsub
bfss: directories $(TARGET_BFSS)
genVarOrder: directories $(TARGET_ORDR)
readCnf: directories $(TARGET_RCNF)
verify: directories $(TARGET_VRFY)
revsub: directories $(TARGET_RSUB)

directories:
	@mkdir -p $(OBJDIR)
	@mkdir -p $(BINDIR)

$(TARGET_BFSS): $(BFSS_OBJECTS)
	$(CXX) $(CPP_FLAGS) -o $@ $^ $(LFLAGS)
	@echo "Built Target! - bfss"

$(TARGET_ORDR): $(ORDR_OBJECTS)
	$(CXX) $(CPP_FLAGS) -o $@ $^ $(LFLAGS)
	@echo "Built Target! - genVarOrder"

$(TARGET_RCNF): $(RCNF_SOURCES)
	$(CXX) $(CPP_FLAGS) $^ -o $@
	@echo "Compiled "$^" successfully!"
	@echo "Built Target! - readCnf"

$(TARGET_VRFY): $(VRFY_SOURCES)
	$(CXX) $(CPP_FLAGS) $^ -o $@ $(DIR_INCLUDES) $(LIB_ABC) $(LIB_COMMON)
	@echo "Compiled "$^" successfully!"
	@echo "Built Target! - verify"

$(TARGET_RSUB): $(RSUB_SOURCES)
	$(CXX) $^ -o $@
	@echo "Compiled "$^" successfully!"
	@echo "Built Target! - revsub"

$(ALL_OBJECTS): $(OBJDIR)/%.o : $(SRCDIR)/%.cpp
	$(CXX) $(CPP_FLAGS) -c $^ -o $@  $(LFLAGS)
	@echo "Compiled "$<" successfully!"

clean:
	@$(RM) $(BFSS_OBJECTS)
	@echo "Cleanup complete!"

remove: clean
	@$(RM) $(TARGET_BFSS) $(TARGET_ORDR) $(TARGET_RCNF) $(TARGET_VRFY) $(TARGET_RSUB)
	@echo "Executable removed!"
