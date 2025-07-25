#include "operandStack.hpp"


void operandStack::pushInt(int32_t val)
{
    stack.push_back({OperandType::INT, {.intValue = val}});
}

void operandStack::pushFloat(float val)
{
    stack.push_back({OperandType::FLOAT, {.floatValue = val}});
}

void operandStack::pushDouble(double val)
{
    stack.push_back({OperandType::DOUBLE, {.doubleValue = val}});
}

void operandStack::pushBoolean(bool val)
{
    stack.push_back({OperandType::BOOLEAN_VALUE, {.boolValue = val}});
}

void operandStack::pushRef(PAGNode* ref)
{
    stack.push_back({OperandType::REFERENCE, {.refValue = ref}});
}

void operandStack::push(StackFrame s)
{
    stack.push_back(s);
}
void operandStack::pushLong(int64_t val)
{
    // Push the actual long value. It conceptually occupies two slots.
    stack.push_back({OperandType::LONG, {.longValue = val}});
    // Per JVM spec, a placeholder is often considered for the second slot.
    // In a simple simulator, you might push a second, empty value
    // or just handle the indexing logic correctly in your pop functions.
    // For simplicity, we'll let pop handle the two-slot logic.
}

StackFrame operandStack::pop() 
{
    
    TR_ASSERT_FATAL(!stack.empty(),"Operand stack underflow");

    StackFrame top = stack.back();
    stack.pop_back();

    return top;
}

int32_t operandStack::popInt() {
    StackFrame val = pop();
    TR_ASSERT_FATAL(val.type == OperandType::INT,"Type error: Expected INT on stack");
    return val.value.intValue;
}

float operandStack::popFloat() {
    StackFrame val = pop();
    TR_ASSERT_FATAL(val.type == OperandType::FLOAT,"Type error: Expected FLOAT on stack");
    return val.value.floatValue;
}
int64_t operandStack::popLong() {
    StackFrame val = pop();
    TR_ASSERT_FATAL(val.type == OperandType::LONG,"Type error: Expected LONG on stack");
    
    return val.value.longValue;
}

double operandStack::popDouble() {
    StackFrame val = pop();
    TR_ASSERT_FATAL(val.type == OperandType::DOUBLE,"Type error: Expected DOUBLE on stack");
    return val.value.doubleValue;
}
bool operandStack::popBoolean() {
    StackFrame val = pop();
    TR_ASSERT_FATAL(val.type == OperandType::BOOLEAN_VALUE,"Type error: Expected BOOLEAN on stack");
    return val.value.boolValue;
}

PAGNode* operandStack::popRef() {
    StackFrame val = pop();
    TR_ASSERT_FATAL(val.type == OperandType::REFERENCE,"Type error: Expected REFERENCE on stack");
    return val.value.refValue;
}