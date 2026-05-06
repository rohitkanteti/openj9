#pragma once
#include <vector>
#include <set>
#include "../../../../../omr/compiler/optimizer/PAG/PointerAssignmentGraph.hpp"
#include <cstdint>
#include <cassert>

enum class OperandType
{
    INT,
    LONG,
    FLOAT,
    DOUBLE,
    BOOLEAN_VALUE,
    REFERENCE
};

struct StackFrame
{
    OperandType type;
    union
    {
        int32_t intValue;
        int64_t longValue;
        float floatValue;
        double doubleValue;
        bool boolValue;
        PAGNode *refValue;
    } value;

    bool operator<(const StackFrame &other) const
    {
        if (type != other.type)
            return type < other.type;
        switch (type)
        {
        case OperandType::INT:
            return value.intValue < other.value.intValue;
        case OperandType::LONG:
            return value.longValue < other.value.longValue;
        case OperandType::FLOAT:
            return value.floatValue < other.value.floatValue;
        case OperandType::DOUBLE:
            return value.doubleValue < other.value.doubleValue;
        case OperandType::BOOLEAN_VALUE:
            return value.boolValue < other.value.boolValue;
        case OperandType::REFERENCE:
            return value.refValue < other.value.refValue;
        }
        return false;
    }

    bool isRefOfClass(const std::string &className) const
    {
        if (type != OperandType::REFERENCE || value.refValue == nullptr)
        {
            return false;
        }
        return value.refValue->comp_type.rfind(className, 0) == 0;
    }
};

class operandStack
{
public:
    operandStack() = default;

    operandStack(const operandStack &other);
    operandStack &operator=(const operandStack &other);

    void pushInt(int32_t val);
    void pushLong(int64_t val);
    void pushFloat(float val);
    void pushDouble(double val);
    void pushBoolean(bool val);
    void pushRef(PAGNode *ref);
    void push(const std::set<StackFrame> &s);
    void push(const std::set<PAGNode *> &s);

    std::set<StackFrame> pop();
    std::set<StackFrame> pop(std::string fullNAME);
    std::set<int32_t> popInt(std::string fullNAME);
    std::set<int64_t> popLong(std::string fullNAME);
    std::set<float> popFloat(std::string fullNAME);
    std::set<double> popDouble(std::string fullNAME);
    std::set<bool> popBoolean(std::string fullNAME);
    std::set<PAGNode *> popRef(std::string fullNAME);
    bool merge(const operandStack &other,std::string,int);

private:
    std::vector<std::set<StackFrame>> stack;
};
