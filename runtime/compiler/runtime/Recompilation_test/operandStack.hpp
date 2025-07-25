#pragma once
#include "../../../../../omr/compiler/optimizer/PAG/PointerAssignmentGraph.hpp"
#include <vector>

enum class OperandType {
    EMPTY,     
    INT,
    LONG,
    FLOAT,
    DOUBLE,
    BOOLEAN_VALUE,
    REFERENCE    
};
   
struct StackFrame {
    OperandType type;
    union {
        int32_t  intValue;
        int64_t  longValue;
        float    floatValue;
        double   doubleValue;
        bool boolValue;
        PAGNode*    refValue; // Represents an object reference
    } value;
};

#include "operandStack.hpp"

class operandStack
{
 public:
    std::vector<StackFrame> stack;

    void push(StackFrame s);
    void pushInt(int32_t val);
    void pushFloat(float val);
    void pushBoolean(bool val);
    void pushDouble(double val);
    void pushRef(PAGNode* ref);

    void pushLong(int64_t val);

    StackFrame pop() ;

    int32_t popInt() ;
    float popFloat();
    double popDouble();
    int64_t popLong() ;
    bool popBoolean();
    PAGNode* popRef() ;

};