#include "operandStack.hpp"


void operandStack::pushInt(int32_t val) {
    stack.push_back({ StackFrame{OperandType::INT, {.intValue = val}} });
}

void operandStack::pushLong(int64_t val) {
    stack.push_back({ StackFrame{OperandType::LONG, {.longValue = val}} });
}

void operandStack::pushFloat(float val) {
    stack.push_back({ StackFrame{OperandType::FLOAT, {.floatValue = val}} });
}

void operandStack::pushDouble(double val) {
    stack.push_back({ StackFrame{OperandType::DOUBLE, {.doubleValue = val}} });
}

void operandStack::pushBoolean(bool val) {
    stack.push_back({ StackFrame{OperandType::BOOLEAN_VALUE, {.boolValue = val}} });
}

void operandStack::pushRef(PAGNode* ref) {
    stack.push_back({ StackFrame{OperandType::REFERENCE, {.refValue = ref}} });
}

void operandStack::push(const std::set<StackFrame> &s) {
    stack.push_back(s);
}
void operandStack::push(const std::set<PAGNode*> &s) {
    std::set<StackFrame> ss;
    for(PAGNode* node:s)
    {
        ss.insert({ StackFrame{OperandType::REFERENCE, {.refValue = node}} });
    }
    push(ss);
}

// === Pop ===

std::set<StackFrame> operandStack::pop(std::string fullNAME) {
    if(stack.empty()) {
        
    }
    TR_ASSERT_FATAL(!stack.empty(), "Operand stack underflow");
    auto top = stack.back();
    stack.pop_back();
    return top;
}


std::set<int32_t> operandStack::popInt(std::string fullNAME) {
    auto vals = pop(fullNAME);
    std::set<int32_t> results;
    for (auto &sf : vals) {
        TR_ASSERT_FATAL(sf.type == OperandType::INT, "Expected INT");
        results.insert(sf.value.intValue);
    }
    return results;
}

std::set<int64_t> operandStack::popLong(std::string fullNAME) {
    auto vals = pop(fullNAME);
    std::set<int64_t> results;
    for (auto &sf : vals) {
        TR_ASSERT_FATAL(sf.type == OperandType::LONG, "Expected LONG");
        results.insert(sf.value.longValue);
    }
    return results;
}

std::set<float> operandStack::popFloat(std::string fullNAME) {
    auto vals = pop(fullNAME);
    std::set<float> results;
    for (auto &sf : vals) {
        TR_ASSERT_FATAL(sf.type == OperandType::FLOAT, "Expected FLOAT");
        results.insert(sf.value.floatValue);
    }
    return results;
}

std::set<double> operandStack::popDouble(std::string fullNAME) {
    auto vals = pop(fullNAME);
    std::set<double> results;
    for (auto &sf : vals) {
        TR_ASSERT_FATAL(sf.type == OperandType::DOUBLE, "Expected DOUBLE");
        results.insert(sf.value.doubleValue);
    }
    return results;
}

std::set<bool> operandStack::popBoolean(std::string fullNAME) {
    auto vals = pop(fullNAME);
    std::set<bool> results;
    for (auto &sf : vals) {
        TR_ASSERT_FATAL(sf.type == OperandType::BOOLEAN_VALUE, "Expected BOOLEAN");
        results.insert(sf.value.boolValue);
    }
    return results;
}

std::set<PAGNode*> operandStack::popRef(std::string fullNAME) {
    auto vals = pop(fullNAME);
    std::set<PAGNode*> results;
    for (auto &sf : vals) {
        TR_ASSERT_FATAL(sf.type == OperandType::REFERENCE, "Expected REFERENCE");
        results.insert(sf.value.refValue);
    }
    return results;
}

operandStack::operandStack(const operandStack &other)
    : stack(other.stack) // deep copy of vector<set<StackFrame>>
    {}
 
operandStack& operandStack::operator=(const operandStack &other) {
    if (this != &other) {
        stack = other.stack; // deep copy
    }
    return *this;
}


bool operandStack::merge(const operandStack &other,std::string fullNAME,int startBCI)
{   
    if(stack.size() != other.stack.size())
    {
        std::cout << "stacks not equal while analyzing " << fullNAME << " at BCI " << startBCI << std::endl;
        std::cout << "Current stack size: " << stack.size() << ", Other stack size: " << other.stack.size() << std::endl;
    }
    TR_ASSERT_FATAL(stack.size() == other.stack.size(),"Merging stacks of different heights is not supported");

    bool changed = false;

    for (size_t i = 0; i < stack.size(); i++) {
        size_t oldSize = stack[i].size();

        stack[i].insert(other.stack[i].begin(), other.stack[i].end());

        if (stack[i].size() != oldSize)
            changed = true;
    }

    return changed;
}

