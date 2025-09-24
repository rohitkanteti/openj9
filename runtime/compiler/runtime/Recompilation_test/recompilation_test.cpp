#pragma once
#include "../../../../../omr/compiler/optimizer/PAG/PointerAssignmentGraph.hpp"
#include "../../../../../omr/compiler/optimizer/PAG/CallGraph.hpp"
#include "../../control/J9CompilationStrategy.hpp"
#include "../../../../../omr/compiler/control/CompilationController.hpp"
#include "../../control/CompilationRuntime.hpp"
#include "../../ilgen/J9ByteCodeIterator.hpp"
#include "j9nonbuilder.h"
#include <unordered_set>
#include <queue>
#include <set>
#include <vector>
#include "../RelocationRuntime.hpp"
#include <j9.h>
#include "j9cp.h"
#include "j9consts.h"
#include "j9protos.h"
#include "j9vmnls.h"
#include "operandStack.hpp"
#include <string.h>
#include <fstream>
#include "env/VMAccessCriticalSection.hpp"
#include "../../../../../omr/gc/structs/PoolIterator.hpp"

#define STATIC_FIELD_READ -10866 // unique negative code for static field read.
#define RETURN_NODE_NAME -56765  // UNIQUE NAME for return node

int globalIndex = 0;
extern TR_ResolvedMethod *getCachedResolvedMethodFromPtr(TR::Compilation *comp, TR_OpaqueMethodBlock *methodPtr);
extern bool returnsObject(const std::string &methodSignature);
extern bool isLibraryMethod(std::string methodName);
extern std::unordered_set<std::string> getClassFields(J9Class *clazz, J9VMThread *vmThread);
extern std::unordered_set<std::string> getReflectiveTargets(std::string &caller, int lineNumber);
static std::unordered_set<std::string> analysedMethodNames;
static unordered_set<std::string> threadExtendingClasses;
static std::unordered_map<std::string, std::unordered_set<std::string>> className_to_fields;
extern void getResolvedReflectiveCalls();
static std::unordered_map<std::string, PAGNode *> class_to_staticPAGNode;
struct CallInfo
{
    std::string callee;
    int lineNumber;

    CallInfo(const std::string &callee, int line)
        : callee(callee), lineNumber(line) {}
};
static std::unordered_map<std::string, std::vector<CallInfo>> reflectiveCallGraph;
static unordered_set<std::string> all_loaded_classes;
static bool threadClassesIdentified = false;
std::unordered_set<std::string> changedMethodNames;

PointerAssignmentGraph *pag_to_use = nullptr;
class recompilation_test
{
public:
    TR_RelocationRuntime *reloRuntime;

    int getOrInsertMethodIndex(std::string methodName, PointerAssignmentGraph *pag)
    {
        // TR_OpaqueMethodBlock *methodPersistentId = methodSymbol->getResolvedMethod()->getPersistentIdentifier();
        // // no need of assert, guaranteed to be available

        if (pag->_methodIndices.find(methodName) != pag->_methodIndices.end())
        {
            std::cout << "Found in the method indices " << methodName << std::endl;
            return pag->_methodIndices[methodName];
        }

        int index = pag->_methodIndices.size() + 1;
        pag->_methodIndices[methodName] = index;
        std::cout << "Inserted in the method indices " << methodName << std::endl;

        return index;
    }
    // boolean should_recompile(Method mx,Method,PAG p_prime,PAG p)
    bool should_recompile(int mx, PointerAssignmentGraph *p_prime, unordered_set<PAGEdge *> old_allocated_edges, unordered_set<PAGNode *> old_escaping_objects)
    {
        // Get allocated objects in mx
        // auto old_allocated_edges = p->getAllocEdges(mx); // E: o1 --NEW--> temp, for stmt `temp: new A()` in il-trees

        // Get escaping objects in mx in p
        // auto old_escaping_objects = p->getEscapingObjects(mx);

        // Get leaky nodes in the updated PAG p'
        auto leaky_nodes = p_prime->getLeakyNodes();

        for (PAGEdge *alloc_edge : old_allocated_edges)
        {
            PAGNode *o = alloc_edge->src;
            bool isEscaping = std::find(old_escaping_objects.begin(), old_escaping_objects.end(), o) != old_escaping_objects.end();

            if (isEscaping)
            {
                // Ensure no reachable path from any leaky node
                bool isReachable = false;

                // [ \forall u \in leaky_nodes , ~REACH(o,u) ] => recompile mx
                for (PAGNode *u : leaky_nodes)
                {
                    isReachable |= REACH(o, u, p_prime);
                }

                if (isReachable == false)
                    return true; // Recompile mx
            }
            else
            {
                // \exists u \in leaky_nodes , REACH(o,u) => recompile mx
                for (PAGNode *u : leaky_nodes)
                {
                    if (REACH(o, u, p_prime))
                    {
                        return true; // Recompile mx
                    }
                }
            }
        }

        return false; // No recompilation needed
    }

    PointerAssignmentGraph *update_PAG(PointerAssignmentGraph *p, int my, J9Method *my_prime_J9Method, CallGraph *CG)
    {

        std::cout << "The index my is = " << my << std::endl;
        if (analysedMethodNames.empty())
        {
            // getAnalyzedMethods();
        }
        if (all_loaded_classes.empty())
        {
            getall_loaded_classes(reloRuntime->comp());
        }
        if (!threadClassesIdentified)
        {
            threadClassesIdentified = true;
            getResolvedReflectiveCalls();
            getThreadRelatedClasses(reloRuntime->comp());
        }
        // remove intraprocedural edges [All the edges to formal params are `assign` edges]
        for (PAGNode *f_param : p->getFormalParameterNodes(my))
        {
            p->removeAllEdgesFrom(f_param);
        }

        // for (int caller : CG->getCallers(my))
        // {
        //     for (auto cs : CG->getCallSites(caller, my))
        //     {
        //         std::cout << "caller= " << caller << "cs= " << cs << std::endl;

        //         PAGNode *ret_my = p->getReturnNode(my);
        //         if (ret_my != NULL)
        //         {
        //             // remove edge from the x labelled by the callsite cs
        //             int nodeIndex = p->callsite_to_storeNodeIndex[cs];
        //             PAGNode *x = p->nodeIndexToNode[nodeIndex];
        //             std::cout << x << std::endl;
        //             if (x)
        //             {
        //                 p->removeEdgeFrom(x, cs); // check this !!
        //             }
        //             p->removeAllEdgesFrom(ret_my);
        //         }
        //         for (PAGNode *a_param : p->getActualParameterNodes(my, cs))
        //         {
        //             // remove edge from the actual paramter labelled by the callsite cs
        //             p->removeEdgeFrom(a_param, cs);
        //         }
        //     }
        // }

        // remove match edges -- UPDATED TO REMOVE ALL INTRAPROCEDURAL EDGES IN ONE METHOD
        // for (PAGEdge *e1 : p->getStoreEdges(my))
        // {
        //     for (PAGEdge *e2 : p->getLoadEdges(my))
        //     {
        //         if (e1->field == e2->field)
        //         {
        //             p->removeEdgeFrom(e1->src, MATCH);
        //             p->removeEdgeFrom(e2->dest, MATCH_BAR);
        //         }
        //     }
        // }

        // remove intraprocedural edges
        // Assume remove call will remove both edges labelled by k and k_bar
        p->removeEdges(my); // This will remove all the edges that are having a source as a node created in my
        p->removeNodes(my);

        // add intraprocedural edges
        // Assume addEdge(flowsToSrc,flowsToTarget,label) call with label k
        // will also add the reverse edge with label k_bar
        // TODO: add intraprocedural edges
        // use computeMSetForMethod(TR::Compilation *comp, TR::ResolvedMethodSymbol *methodSymbol)
        // computeMsetForMethod call will create all the nodes for actual/formal and return nodes and also add the edges(both intra/inter)
        TR::Compilation *comp = reloRuntime->comp();

        // printMethodBytecodeStatements(my_prime_J9Method, resolvedMethod, comp);

        // the method index for my and my' must be the same.

        // traverse_bytecode(my_prime_J9Method, p, my, reloRuntime->comp());

        // J9JavaVM* vm = reloRuntime->javaVM();
        // if(vm)
        // {
        //     J9JITConfig *jitConfig = vm->jitConfig;
        //     if(jitConfig)
        //     {
        //           TR::CompilationInfo * compInfo = getCompilationInfo(jitConfig);
        //           if(compInfo)
        //           {
        //             J9Method *ramMethod = reinterpret_cast<J9Method*>(my_prime_J9Method);
        //             J9ROMMethod *romMethod = J9_ROM_METHOD_FROM_RAM_METHOD(ramMethod);

        //             if (!(romMethod->modifiers & (J9AccAbstract | J9AccNative)))
        //             {
        //                 // TR_OptimizationLevel optLevel = warm; // or cold, hot, etc.
        //                 J9VMThread* vmThread = vm->mainThread;
        //                 TR::IlGeneratorMethodDetails details(ramMethod);
        //                 bool queued = false;
        //                 TR_MethodEvent event;
        //                 void *oldStartPC = NULL;
        //                 event._eventType = TR_MethodEvent::InterpreterCounterTripped;

        //                 event._j9method = ramMethod;
        //                 event._oldStartPC = oldStartPC;
        //                 event._vmThread = vmThread;
        //                 event._classNeedingThunk = 0;
        //                 bool newPlanCreated;
        //                 IDATA result = 0;
        //                 TR_OptimizationPlan *plan = TR::CompilationController::getCompilationStrategy()->processEvent(&event, &newPlanCreated);
        //                 result = (IDATA)compInfo->compileMethod(vmThread, details, oldStartPC, async, compErrCode, &queued, plan);
        //             }
        //           }
        //     }

        // }

        // bool ilGenFailed = NULL == resolvedMethod->genMethodILForPeekingEvenUnderMethodRedefinition(methodSymbol, comp, false);
        // TR_ASSERT_FATAL(!ilGenFailed, "IL Gen failed for my_prime");

        // add interprocedural edges
        // auto f_params = p->getFormalParameterNodes(my_prime); // These should not change from my to my_prime
        // for (auto caller : CG->getCallers(my)) {
        //     for (auto cs : CG->getCallSites(caller, my_prime)) {

        //         //TODO create
        //         auto a_params = p->createParameterNodes(my_prime,cs);
        //         auto ret_my =   p->createReturnNode(my_prime);  // null if the callsite doesnot return anything

        //         for (int i = 0; i < f_params.size(); i++) {
        //             p->addEdge(a_params[i], f_params[i], ASSIGN,cs); // assign[i]
        //         }

        //         if (ret_my != nullptr) {

        //             PAGNode* x = p->nodeIndexToNode[p->callsite_to_storeNodeIndex[cs]];
        //             p->addEdge(ret_my, x,ASSIGN,cs); // assign[i] to x
        //         }
        //     }
        // }

        // add match edges
        // for (PAGEdge *e1 : p->getStoreEdges(my))
        // {
        //     for (PAGEdge *e2 : p->getLoadEdges(my))
        //     {
        //         if (e1->field == e2->field)
        //         {
        //             p->addEdge(e1->src, e2->dest, MATCH);
        //         }
        //     }
        // }

        return p;
    }

    // set<string> get_fields(AbstractNode obj)
    std::unordered_set<std::string> get_fields(PointerAssignmentGraph *p, PAGNode *obj)
    {
        std::unordered_set<string> fields;
        // if there is a putfield to this node then its having a field labelled in the edge label
        for (PAGNode *node : p->flowsTo(obj))
        {
            for (PAGEdge *e : p->getStoreEdges())
            {
                if (e->dest == node)
                {
                    fields.insert(e->field);
                }
            }
        }
        return fields;
    }

    // set<AbstractNodes> get_field_target(AbstractNode current_obj, string field)
    std::unordered_set<PAGNode *> get_field_target(PointerAssignmentGraph *p, PAGNode *obj, std::string field)
    {
        std::unordered_set<PAGNode *> targets;
        for (PAGEdge *e : p->getStoreEdges())
        {
            if (e->dest == obj && e->field == field)
            {
                targets.insert(e->src);
            }
        }
        return targets;
    }

    bool isStaticField(std::string field, PointerAssignmentGraph *p)
    {

        return p->staticFields.find(field) != p->staticFields.end();
    }

    bool isThreadClassField(std::string field, PointerAssignmentGraph *p)
    {

        return p->threadAccessibleFields.find(field) != p->threadAccessibleFields.end();
    }

    // boolean REACH(Node target_obj, Node start_node, PAG p):
    bool REACH(PAGNode *target_obj, PAGNode *start_node, PointerAssignmentGraph *p)
    {
        // Case 1:
        std::unordered_set<PAGNode *> objs = p->points_to(start_node);

        // if(objs.size() == 1)
        // {
        //     for(auto* ob : objs)
        //     {
        //         std::cout << "ob "<< ob << std::endl;
        //     }
        //     std::cout << "target ob " <<  target_obj << std::endl;
        //     std::cout << "start node   " <<  start_node << std::endl;

        // }
        if (objs.find(target_obj) != objs.end())
            return true;
        std::set<std::pair<PAGNode *, std::vector<std::string>>> visited;

        // Queue for BFS traversal (object, field_path)
        std::queue<std::pair<PAGNode *, std::vector<std::string>>> queue;

        // Enqueue all objects directly pointed to by start_node
        for (PAGNode *obj : objs)
        {
            queue.push({obj, {}});
            visited.insert({obj, {}});
        }

        while (!queue.empty())
        {
            auto front = queue.front();
            auto current_obj = front.first;
            auto field_path = front.second;
            queue.pop();

            // Check if current object matches target_obj
            if (current_obj == target_obj)
                return true;

            // Explore fields of the current object
            for (std::string field : p->get_fields(current_obj))
            {

                auto next_objs = p->get_field_target(current_obj, field);
                auto new_field_path = field_path;
                new_field_path.push_back(field);

                for (PAGNode *next_obj : next_objs)
                {
                    auto path_key = std::make_pair(next_obj, new_field_path);

                    if (visited.find(path_key) == visited.end())
                    {
                        visited.insert(path_key);
                        queue.push({next_obj, new_field_path});
                    }

                    // Check if this path reaches target_obj
                    if (next_obj == target_obj)
                        return true;
                }
            }
        }

        return false;
    }

//     void traverse_bytecode(J9Method *method, PointerAssignmentGraph *pag, int methodIndex, TR::Compilation *comp)
//     {

//         TR_OpaqueMethodBlock *method_block = reinterpret_cast<TR_OpaqueMethodBlock *>(method);
//         int32_t methodSize = TR::Compiler->mtd.bytecodeSize(method_block);
//         uintptr_t methodStart = TR::Compiler->mtd.bytecodeStart(method_block);
//         TR_ResolvedMethod *resolvedMethod = getCachedResolvedMethodFromPtr(comp, method_block);

//         char *classNameChars = resolvedMethod->classNameChars();
//         int32_t classNameLength = resolvedMethod->classNameLength();

//         char *methodName = resolvedMethod->nameChars();
//         int32_t methodNameLength = resolvedMethod->nameLength();
//         char *methodSignature = resolvedMethod->signatureChars();
//         int32_t methodSignatureLength = resolvedMethod->signatureLength();

//         std::string name(methodName, methodNameLength);
//         std::string className(classNameChars, classNameLength);
//         std::string signature(methodSignature, methodSignatureLength);

//         bool hasReturnType = returnsObject(methodSignature);
//         if(isLibraryMethod((className+"."+name+signature)))   
//         {
//             std::cout << "############## SKIPPED Traversing the Bytecode of the method " << className << "." << name << signature << "##############" << std::endl;
//             return;
//         } 
//         std::cout << "############## Traversing the Bytecode of the method " << className << "." << name << signature << "##############" << std::endl;
//         int num_params = count_parameters(methodSignature); // resolvedMethod->numberOfParameterSlots(); double or long takes 2 slots so cannot realy on this
//         std::unordered_map<int, PAGNode *> variableMap;
//         int reference_params = 0;
//         std::string fullNAME = className + "." + name + signature;
//         // Create entries in the varaible Map for each of the parameters and a PAGNode for return node ;
//         if (analysedMethodNames.find(fullNAME) == analysedMethodNames.end()) // This means that this method 'my' was not analyzed before or called before.
//         {
//             for (int i = num_params - 1; i >= 0; i--)
//             {
//                 if (is_reference_type(methodSignature, i))
//                 {   
//                     reference_params++;
//                     PAGNode *param_node_ptr = new PAGNode(VARIABLE, i, nullptr, method_block, -1, methodIndex);
//                     std::cout << "Method index = " << methodIndex << std::endl;
//                     pag->methodIndex_to_allMethodNodes[methodIndex].push_back(param_node_ptr);
//                     pag->PAG_nodes.insert(param_node_ptr);
//                     pag->methodIndex_to_formalNodes[methodIndex].push_back(param_node_ptr);
//                 }
//             }
//             if (!resolvedMethod->isStatic())
//             {
//                 PAGNode *param_node_ptr = new PAGNode(VARIABLE,3550, nullptr, method_block, -1, methodIndex);
//                 std::cout << "Method index = " << methodIndex << std::endl;
//                 pag->methodIndex_to_allMethodNodes[methodIndex].push_back(param_node_ptr);
//                 pag->PAG_nodes.insert(param_node_ptr);
//                 pag->methodIndex_to_formalNodes[methodIndex].push_back(param_node_ptr);
//                 reference_params++;
//             }
//             if (hasReturnType)
//             {
//                 pag->methodIndex_to_returnNode[methodIndex] = new PAGNode(RETURN, RETURN_NODE_NAME, NULL, method_block, -1, methodIndex);
//                 pag->PAG_nodes.insert(pag->methodIndex_to_returnNode[methodIndex]);
//                 pag->methodIndex_to_allMethodNodes[methodIndex].push_back(pag->methods_to_returnNode[methodIndex]);
//             }
//         }
//         vector<PAGNode *> formal_param_nodes = pag->methodIndex_to_formalNodes[methodIndex];
//         PAGNode *returnNode = nullptr;
//         auto it = pag->methodIndex_to_returnNode.find(methodIndex);
//         if (it != pag->methodIndex_to_returnNode.end())
//         {
//             returnNode = it->second;
//         }

//         std::cout << "Formal params size = " << formal_param_nodes.size() << std::endl;
//         if (reference_params != formal_param_nodes.size() || ((hasReturnType && !returnNode) || (!hasReturnType && returnNode)))
//         {
//             throw std::runtime_error("There is a mismatch in the size of paramters maybe the method signature changed.");
//         }

//         for (int i = 0; i < reference_params; i++)
//         {
//             // PAGNode *param_node_ptr = new PAGNode(VARIABLE, i, nullptr, method_block, -1, methodIndex);
//             // pag->methods_to_allMethodNodes[methodIndex].push_back(param_node_ptr);
//             // pag->PAG_nodes.insert(param_node_ptr);
//             // pag->methods_to_formalNodes[methodIndex].push_back(param_node_ptr);

//             variableMap[i] = formal_param_nodes[i];
//         }
//         if (hasReturnType)
//         {
//             // pag->methods_to_returnNode[methodIndex] = new PAGNode(RETURN, RETURN_NODE_NAME, NULL, method_block, -1, methodIndex);
//             // pag->PAG_nodes.insert(pag->methods_to_returnNode[methodIndex]);
//             // pag->methods_to_allMethodNodes[methodIndex].push_back(pag->methods_to_returnNode[methodIndex]);
//         }

//         int32_t currentIndex = 0;
//         int statementCount = 0;
//         operandStack *stack = new operandStack();

//         while (currentIndex < methodSize)
//         {
//             TR_ASSERT_FATAL(currentIndex >= 0 && currentIndex < methodSize, "Bytecode index out of bounds");

//             uint8_t *pc = (uint8_t *)(methodStart + currentIndex);

//             TR_J9ByteCode bytecode = TR_J9ByteCodeIterator::convertOpCodeToByteCodeEnum(*pc);
//             int32_t instructionLength = getInstructionLength(bytecode, pc);
//             std::cout << "  [" << statementCount << "] PC: " << currentIndex
//                       << " - Opcode: 0x" << std::hex << (int)(*pc) << std::dec
//                       << " - " << getBytecodeString(bytecode) << " ---> " << instructionLength << std::endl;

//             executeBytecode(bytecode, pc, pag, stack, resolvedMethod, method, methodIndex, currentIndex, variableMap, hasReturnType, comp);

//             // if (bytecode == J9BCnew)
//             // {
//             //     uint16_t cpIndex = (pc[2] << 8) | pc[1];
//             //     uint32_t classNamelength = 0;
//             //     char *classNameChars = resolvedMethod->getClassNameFromConstantPool(cpIndex, classNamelength);
//             //     std::string className(classNameChars, classNamelength);
//             //     std::cout << "  -> Create an object of type: " << className << std::endl;
//             // }

//             // if (bytecode == J9BCgetfield || bytecode == J9BCputfield)
//             // {

//             //     uint16_t cpIndex = (pc[2] << 8) | pc[1];
//             //     int fieldNameLength = 0;
//             //     const char *fieldNameChars = resolvedMethod->fieldNameChars(cpIndex, fieldNameLength);

//             //     std::string fieldName(fieldNameChars, fieldNameLength);

//             //     int signatureLength = 0;
//             //     const char *signatureChars = resolvedMethod->fieldSignatureChars(cpIndex, signatureLength);

//             //     std::string signature(signatureChars, signatureLength - 1);
//             //     signature = signature.substr(1);

//             //     // int classNamelength = 0;
//             //     // const char *className = resolvedMethod->classNameOfFieldOrStatic(cpIndex,classNamelength);

//             //     std::cout << "  -> Access the field: " << signature << "." << fieldName;
//             // }
//             // std::cout << std::endl;

//             currentIndex += instructionLength;
//             globalIndex++;
//             statementCount++;
//         }

//         std::string fully_qualified_name = className + "." + name + signature;
//         if (changedMethodNames.find(fully_qualified_name) != changedMethodNames.end())
//         {
//             changedMethodNames.erase(fully_qualified_name);
//         }
//         analysedMethodNames.insert(fully_qualified_name);
//     }

//     void printMethodBytecodeStatements(TR_OpaqueMethodBlock *method, TR_ResolvedMethod *resolvedMethod, TR::Compilation *comp)
//     {

//         int32_t methodSize = TR::Compiler->mtd.bytecodeSize(method);
//         uintptr_t methodStart = TR::Compiler->mtd.bytecodeStart(method);

//         std::cout << "Bytecode size: " << methodSize << " bytes" << " - number of parameters = " << resolvedMethod->numberOfParameterSlots() << std::endl;
//         std::cout << "Bytecode statements:" << std::endl;

//         int32_t currentIndex = 0;
//         int statementCount = 0;

//         while (currentIndex < methodSize)
//         {
//             TR_ASSERT_FATAL(currentIndex >= 0 && currentIndex < methodSize,
//                             "Bytecode index out of bounds");

//             uint8_t *pc = (uint8_t *)(methodStart + currentIndex);

//             TR_J9ByteCode bytecode = TR_J9ByteCodeIterator::convertOpCodeToByteCodeEnum(*pc);

//             std::cout << "  [" << statementCount << "] PC: " << currentIndex
//                       << " - Opcode: 0x" << std::hex << (int)(*pc) << std::dec
//                       << " - " << getBytecodeString(bytecode); //<< "--- cpIndex = " << static_cast<int>((pc[2] << 8) | pc[1]);
//             if (bytecode == J9BCnew)
//             {
//                 uint16_t cpIndex = (pc[2] << 8) | pc[1];
//                 uint32_t classNamelength = 0;
//                 char *classNameChars = resolvedMethod->getClassNameFromConstantPool(cpIndex, classNamelength);
//                 std::string className(classNameChars, classNamelength);
//                 std::cout << "  -> Create an object of type: " << className << std::endl;
//             }
//             else if (bytecode == J9BCinvokevirtual)
//             {
//                 uint16_t cpIndex = (pc[1] << 8) | pc[2];
//                 std::cout << "opcode = 0x"
//                           << std::hex << +pc[0]
//                           << std::dec << std::endl;

//                 std::cout << "\npc[1] = " << static_cast<int>(pc[1])
//                           << ", pc[2] = " << static_cast<int>(pc[2])
//                           << ", (pc[1]<<8)|(pc[2]) = "
//                           << (static_cast<int>(pc[1]) << 8 | static_cast<int>(pc[2]))
//                           << std::endl;

//                 uint classNameLength = 0;
//                 const char *className = resolvedMethod->getClassNameFromConstantPool(cpIndex, classNameLength);
//                 std::cout << " ClassName is " << className << " CpIndex is " << cpIndex << std::endl;
//                 // Get the name of the target method itself.
//                 J9ConstantPool *cp = J9_CP_FROM_METHOD(reinterpret_cast<J9Method *>(resolvedMethod));

//                 J9ROMMethodRef *romMethodRef = (J9ROMMethodRef *)(cp->romConstantPool + cpIndex);
//                 // std::cout << romMethodRef << std::endl;
//                 J9ROMNameAndSignature *nameAndSig = J9ROMMETHODREF_NAMEANDSIGNATURE(romMethodRef); //(J9ROMNameAndSignature*) romMethodRef->nameAndSignature;

//                 //((struct J9ROMNameAndSignature*) (((uint8_t *) &((romMethodRef)->nameAndSignature)) + (J9SRP)((romMethodRef)->nameAndSignature)));//J9ROMMETHODREF_NAMEANDSIGNATURE(romMethodRef);

//                 J9UTF8 *signature = J9ROMNAMEANDSIGNATURE_SIGNATURE(nameAndSig);
//                 J9UTF8 *name = J9ROMNAMEANDSIGNATURE_NAME(nameAndSig);

//                 // J9UTF8 *UTF8_data = J9ROMSTRINGREF_UTF8DATA((J9ROMStringRef *)(&constantPool[cpIndex]));
//                 // J9ROMNameAndSignature *nameAndSig = J9ROMMETHODREF_NAMEANDSIGNATURE(methodRef);

//                 // J9UTF8 *nameUTF8 = J9ROMNAMEANDSIGNATURE_NAME(nameAndSig);

//                 char *methodName = (char *)J9UTF8_DATA(name);
//                 U_16 methodNameLength = J9UTF8_LENGTH(name);
//                 std::string mName(methodName, methodNameLength);
//                 std::cout << "    -> Method:" << mName << std::endl;

//                 char *sigChars = (char *)J9UTF8_DATA(signature);
//                 U_16 sigLength = J9UTF8_LENGTH(signature);
//                 std::string sig(sigChars, sigLength);
//                 std::cout << "    -> signature:" << sig << std::endl;

//                 // // Extract method signature
//                 // J9UTF8 *sigUTF8 = J9ROMNAMEANDSIGNATURE_SIGNATURE(nameAndSig);
//                 // char *signature = (char*)J9UTF8_DATA(sigUTF8);
//                 // U_16 sigLength = J9UTF8_LENGTH(sigUTF8);

//                 // Print method name and signature
//                 // printf("    -> Method: %.*s%.*s\n", methodNameLength, methodName, sigLength, signature);
//             }

//             if (bytecode == J9BCgetfield || bytecode == J9BCputfield)
//             {

//                 uint16_t cpIndex = (pc[2] << 8) | pc[1];
//                 int fieldNameLength = 0;
//                 const char *fieldNameChars = resolvedMethod->fieldNameChars(cpIndex, fieldNameLength);

//                 std::string fieldName(fieldNameChars, fieldNameLength);

//                 int signatureLength = 0;
//                 const char *signatureChars = resolvedMethod->fieldSignatureChars(cpIndex, signatureLength);

//                 std::string signature(signatureChars, signatureLength - 1);
//                 signature = signature.substr(1);

//                 // int classNamelength = 0;
//                 // const char *className = resolvedMethod->classNameOfFieldOrStatic(cpIndex,classNamelength);

//                 std::cout << "  -> Access the field: " << signature << "." << fieldName;
//             }
//             std::cout << std::endl;

//             int32_t instructionLength = getInstructionLength(bytecode, pc);
//             currentIndex += instructionLength;
//             statementCount++;
//         }

//         std::cout << "Total statements: " << statementCount << std::endl;
//     }

//     const char *getBytecodeString(TR_J9ByteCode bytecode)
//     {
//         switch (bytecode)
//         {
//         case J9BCnop:
//             return "nop";
//         case J9BCaconstnull:
//             return "aconst_null";
//         case J9BCiconstm1:
//             return "iconst_m1";
//         case J9BCiconst0:
//             return "iconst_0";
//         case J9BCiconst1:
//             return "iconst_1";
//         case J9BCiconst2:
//             return "iconst_2";
//         case J9BCiconst3:
//             return "iconst_3";
//         case J9BCiconst4:
//             return "iconst_4";
//         case J9BCiconst5:
//             return "iconst_5";
//         case J9BClconst0:
//             return "lconst_0";
//         case J9BClconst1:
//             return "lconst_1";
//         case J9BCfconst0:
//             return "fconst_0";
//         case J9BCfconst1:
//             return "fconst_1";
//         case J9BCfconst2:
//             return "fconst_2";
//         case J9BCdconst0:
//             return "dconst_0";
//         case J9BCdconst1:
//             return "dconst_1";
//         case J9BCiload:
//             return "iload";
//         case J9BClload:
//             return "lload";
//         case J9BCfload:
//             return "fload";
//         case J9BCdload:
//             return "dload";
//         case J9BCaload:
//             return "aload";

//         case J9BCiload0:
//             return "iload_0";
//         case J9BCiload1:
//             return "iload_1";
//         case J9BCiload2:
//             return "iload_2";
//         case J9BCiload3:
//             return "iload_3";
//         case J9BClload0:
//             return "lload_0";
//         case J9BClload1:
//             return "lload_1";
//         case J9BClload2:
//             return "lload_2";
//         case J9BClload3:
//             return "lload_3";
//         case J9BCfload0:
//             return "fload_0";
//         case J9BCfload1:
//             return "fload_1";
//         case J9BCfload2:
//             return "fload_2";
//         case J9BCfload3:
//             return "fload_3";
//         case J9BCdload0:
//             return "dload_0";
//         case J9BCdload1:
//             return "dload_1";
//         case J9BCdload2:
//             return "dload_2";
//         case J9BCdload3:
//             return "dload_3";
//         case J9BCaload0:
//             return "aload_0";
//         case J9BCaload1:
//             return "aload_1";
//         case J9BCaload2:
//             return "aload_2";
//         case J9BCaload3:
//             return "aload_3";

//         case J9BCiaload:
//             return "iaload";
//         case J9BClaload:
//             return "laload";
//         case J9BCfaload:
//             return "faload";
//         case J9BCdaload:
//             return "daload";
//         case J9BCaaload:
//             return "aaload";
//         case J9BCbaload:
//             return "baload";
//         case J9BCcaload:
//             return "caload";
//         case J9BCsaload:
//             return "saload";

//         case J9BCistore:
//             return "istore";
//         case J9BClstore:
//             return "lstore";
//         case J9BCfstore:
//             return "fstore";
//         case J9BCdstore:
//             return "dstore";
//         case J9BCastore:
//             return "astore";

//         case J9BCistore0:
//             return "istore_0";
//         case J9BCistore1:
//             return "istore_1";
//         case J9BCistore2:
//             return "istore_2";
//         case J9BCistore3:
//             return "istore_3";
//         case J9BClstore0:
//             return "lstore_0";
//         case J9BClstore1:
//             return "lstore_1";
//         case J9BClstore2:
//             return "lstore_2";
//         case J9BClstore3:
//             return "lstore_3";
//         case J9BCfstore0:
//             return "fstore_0";
//         case J9BCfstore1:
//             return "fstore_1";
//         case J9BCfstore2:
//             return "fstore_2";
//         case J9BCfstore3:
//             return "fstore_3";
//         case J9BCdstore0:
//             return "dstore_0";
//         case J9BCdstore1:
//             return "dstore_1";
//         case J9BCdstore2:
//             return "dstore_2";
//         case J9BCdstore3:
//             return "dstore_3";
//         case J9BCastore0:
//             return "astore_0";
//         case J9BCastore1:
//             return "astore_1";
//         case J9BCastore2:
//             return "astore_2";
//         case J9BCastore3:
//             return "astore_3";
//         case J9BCiastore:
//             return "iastore";
//         case J9BClastore:
//             return "lastore";
//         case J9BCfastore:
//             return "fastore";
//         case J9BCdastore:
//             return "dastore";
//         case J9BCaastore:
//             return "aastore";
//         case J9BCbastore:
//             return "bastore";
//         case J9BCcastore:
//             return "castore";
//         case J9BCsastore:
//             return "sastore";

//         case J9BCpop:
//             return "pop";
//         case J9BCpop2:
//             return "pop2";
//         case J9BCdup:
//             return "dup";
//         case J9BCdupx1:
//             return "dup_x1";
//         case J9BCdupx2:
//             return "dup_x2";
//         case J9BCdup2:
//             return "dup2";
//         case J9BCdup2x1:
//             return "dup2_x1";
//         case J9BCdup2x2:
//             return "dup2_x2";
//         case J9BCswap:
//             return "swap";

//         case J9BCiadd:
//             return "iadd";
//         case J9BCladd:
//             return "ladd";
//         case J9BCfadd:
//             return "fadd";
//         case J9BCdadd:
//             return "dadd";
//         case J9BCisub:
//             return "isub";
//         case J9BClsub:
//             return "lsub";
//         case J9BCfsub:
//             return "fsub";
//         case J9BCdsub:
//             return "dsub";
//         case J9BCimul:
//             return "imul";
//         case J9BClmul:
//             return "lmul";
//         case J9BCfmul:
//             return "fmul";
//         case J9BCdmul:
//             return "dmul";
//         case J9BCidiv:
//             return "idiv";
//         case J9BCldiv:
//             return "ldiv";
//         case J9BCfdiv:
//             return "fdiv";
//         case J9BCddiv:
//             return "ddiv";
//         case J9BCirem:
//             return "irem";
//         case J9BClrem:
//             return "lrem";
//         case J9BCfrem:
//             return "frem";
//         case J9BCdrem:
//             return "drem";
//         case J9BCineg:
//             return "ineg";
//         case J9BClneg:
//             return "lneg";
//         case J9BCfneg:
//             return "fneg";
//         case J9BCdneg:
//             return "dneg";

//         // Bit operations
//         case J9BCishl:
//             return "ishl";
//         case J9BClshl:
//             return "lshl";
//         case J9BCishr:
//             return "ishr";
//         case J9BClshr:
//             return "lshr";
//         case J9BCiushr:
//             return "iushr";
//         case J9BClushr:
//             return "lushr";
//         case J9BCiand:
//             return "iand";
//         case J9BCland:
//             return "land";
//         case J9BCior:
//             return "ior";
//         case J9BClor:
//             return "lor";
//         case J9BCixor:
//             return "ixor";
//         case J9BClxor:
//             return "lxor";

//         // Control flow
//         case J9BCifeq:
//             return "ifeq";
//         case J9BCifne:
//             return "ifne";
//         case J9BCiflt:
//             return "iflt";
//         case J9BCifge:
//             return "ifge";
//         case J9BCifgt:
//             return "ifgt";
//         case J9BCifle:
//             return "ifle";
//         case J9BCificmpeq:
//             return "if_icmpeq";
//         case J9BCificmpne:
//             return "if_icmpne";
//         case J9BCificmplt:
//             return "if_icmplt";
//         case J9BCificmpge:
//             return "if_icmpge";
//         case J9BCificmpgt:
//             return "if_icmpgt";
//         case J9BCificmple:
//             return "if_icmple";
//         case J9BCifacmpeq:
//             return "if_acmpeq";
//         case J9BCifacmpne:
//             return "if_acmpne";
//         case J9BCifnull:
//             return "ifnull";
//         case J9BCifnonnull:
//             return "ifnonnull";
//         case J9BCgoto:
//             return "goto";
//         case J9BCgotow:
//             return "goto_w";
//         case J9BCtableswitch:
//             return "tableswitch";
//         case J9BClookupswitch:
//             return "lookupswitch";

//         // Method invocation
//         case J9BCinvokevirtual:
//             return "invokevirtual";
//         case J9BCinvokespecial:
//             return "invokespecial";
//         case J9BCinvokestatic:
//             return "invokestatic";
//         case J9BCinvokeinterface:
//             return "invokeinterface";
//         case J9BCinvokedynamic:
//             return "invokedynamic";
//         case J9BCinvokehandle:
//             return "invokehandle";
//         case J9BCinvokehandlegeneric:
//             return "invokehandlegeneric";
//         case J9BCinvokespecialsplit:
//             return "invokespecialsplit";
//         case J9BCinvokestaticsplit:
//             return "invokestaticsplit";
//         case J9BCinvokeinterface2:
//             return "invokeinterface2";

//         // Field access
//         case J9BCgetstatic:
//             return "getstatic";
//         case J9BCputstatic:
//             return "putstatic";
//         case J9BCgetfield:
//             return "getfield";
//         case J9BCputfield:
//             return "putfield";

//         // Object creation and arrays
//         case J9BCnew:
//             return "new";
//         case J9BCnewarray:
//             return "newarray";
//         case J9BCanewarray:
//             return "anewarray";
//         case J9BCmultianewarray:
//             return "multianewarray";
//         case J9BCarraylength:
//             return "arraylength";

//         // Type checking
//         case J9BCcheckcast:
//             return "checkcast";
//         case J9BCinstanceof:
//             return "instanceof";

//         // Exception handling
//         case J9BCathrow:
//             return "athrow";

//         // Synchronization
//         case J9BCmonitorenter:
//             return "monitorenter";
//         case J9BCmonitorexit:
//             return "monitorexit";

//         // Returns
//         case J9BCgenericReturn:
//             return "return generic";
//         case J9BCReturnC:
//             return "ReturnC";
//         case J9BCReturnS:
//             return "ReturnS";
//         case J9BCReturnB:
//             return "ReturnB";
//         case J9BCReturnZ:
//             return "ReturnZ";

//         // Constants loading
//         case J9BCbipush:
//             return "bipush";
//         case J9BCsipush:
//             return "sipush";
//         case J9BCldc:
//             return "ldc";
//         case J9BCldcw:
//             return "ldc_w";
//         case J9BCldc2lw:
//             return "ldc2_w (long)";
//         case J9BCldc2dw:
//             return "ldc2_w (double)";

//         // Conversion instructions
//         case J9BCi2l:
//             return "i2l";
//         case J9BCi2f:
//             return "i2f";
//         case J9BCi2d:
//             return "i2d";
//         case J9BCl2i:
//             return "l2i";
//         case J9BCl2f:
//             return "l2f";
//         case J9BCl2d:
//             return "l2d";
//         case J9BCf2i:
//             return "f2i";
//         case J9BCf2l:
//             return "f2l";
//         case J9BCf2d:
//             return "f2d";
//         case J9BCd2i:
//             return "d2i";
//         case J9BCd2l:
//             return "d2l";
//         case J9BCd2f:
//             return "d2f";
//         case J9BCi2b:
//             return "i2b";
//         case J9BCi2c:
//             return "i2c";
//         case J9BCi2s:
//             return "i2s";

//         // Comparison
//         case J9BClcmp:
//             return "lcmp";
//         case J9BCfcmpl:
//             return "fcmpl";
//         case J9BCfcmpg:
//             return "fcmpg";
//         case J9BCdcmpl:
//             return "dcmpl";
//         case J9BCdcmpg:
//             return "dcmpg";

//         // Increment
//         case J9BCiinc:
//             return "iinc";
//         case J9BCiincw:
//             return "iinc_w";

//         // Wide instructions
//         case J9BCiloadw:
//             return "iload_w";
//         case J9BClloadw:
//             return "lload_w";
//         case J9BCfloadw:
//             return "fload_w";
//         case J9BCdloadw:
//             return "dload_w";
//         case J9BCaloadw:
//             return "aload_w";
//         case J9BCistorew:
//             return "istore_w";
//         case J9BClstorew:
//             return "lstore_w";
//         case J9BCfstorew:
//             return "fstore_w";
//         case J9BCdstorew:
//             return "dstore_w";
//         case J9BCastorew:
//             return "astore_w";
//         case J9BCwide:
//             return "wide";

//         // Special instructions
//         case J9BCasyncCheck:
//             return "asyncCheck";
//         case J9BCbreakpoint:
//             return "breakpoint";
//         case J9BCunknown:
//             return "unknown";

//         default:
//             return "unrecognized";
//         }
//     }

// #include <stdint.h>
//     static int32_t read_int32(uint8_t **pc_ptr)
//     {
//         int32_t val = ((*pc_ptr)[0] << 24) | ((*pc_ptr)[1] << 16) | ((*pc_ptr)[2] << 8) | (*pc_ptr)[3];
//         *pc_ptr += 4;
//         return val;
//     }
//     int32_t calculateTableswitchLength(uint8_t *pc)
//     {
//         uint8_t *current_pc = pc + 1;
//         int32_t padding = (4 - ((intptr_t)pc + 1) % 4) % 4;
//         current_pc += padding;
//         int32_t default_offset = read_int32(&current_pc);
//         int32_t low = read_int32(&current_pc);
//         int32_t high = read_int32(&current_pc);
//         int32_t num_jumps = high - low + 1;
//         current_pc += (num_jumps * 4);
//         return (int32_t)(current_pc - pc);
//     }
//     int32_t calculateLookupswitchLength(uint8_t *pc)
//     {
//         uint8_t *current_pc = pc + 1;
//         int32_t padding = (4 - ((intptr_t)pc + 1) % 4) % 4;
//         current_pc += padding;
//         int32_t default_offset = read_int32(&current_pc);
//         int32_t npairs = read_int32(&current_pc);
//         current_pc += (npairs * 8);
//         return (int32_t)(current_pc - pc);
//     }
//     int32_t calculateWideInstructionLength(uint8_t *pc)
//     {
//         TR_J9ByteCode modified_opcode = (TR_J9ByteCode) * (pc + 1);
//         int32_t length = 1;
//         switch (modified_opcode)
//         {
//         case J9BCiload:
//         case J9BClload:
//         case J9BCfload:
//         case J9BCdload:
//         case J9BCaload:
//         case J9BCistore:
//         case J9BClstore:
//         case J9BCfstore:
//         case J9BCdstore:
//         case J9BCastore:
//             length += 1;
//             length += 2;
//             break;
//         case J9BCiinc:
//             length += 1;
//             length += 2;
//             length += 2;
//             break;
//         default:
//             return -1;
//         }
//         return length;
//     }
//     int32_t getInstructionLength(TR_J9ByteCode bytecode, uint8_t *pc)
//     {
//         switch (bytecode)
//         {
//         case J9BCnop:
//         case J9BCaconstnull:
//         case J9BCiconstm1:
//         case J9BCiconst0:
//         case J9BCiconst1:
//         case J9BCiconst2:
//         case J9BCiconst3:
//         case J9BCiconst4:
//         case J9BCiconst5:
//         case J9BClconst0:
//         case J9BClconst1:
//         case J9BCfconst0:
//         case J9BCfconst1:
//         case J9BCfconst2:
//         case J9BCdconst0:
//         case J9BCdconst1:
//         case J9BCiload0:
//         case J9BCiload1:
//         case J9BCiload2:
//         case J9BCiload3:
//         case J9BClload0:
//         case J9BClload1:
//         case J9BClload2:
//         case J9BClload3:
//         case J9BCfload0:
//         case J9BCfload1:
//         case J9BCfload2:
//         case J9BCfload3:
//         case J9BCdload0:
//         case J9BCdload1:
//         case J9BCdload2:
//         case J9BCdload3:
//         case J9BCaload0:
//         case J9BCaload1:
//         case J9BCaload2:
//         case J9BCaload3:
//         case J9BCiaload:
//         case J9BClaload:
//         case J9BCfaload:
//         case J9BCdaload:
//         case J9BCaaload:
//         case J9BCbaload:
//         case J9BCcaload:
//         case J9BCsaload:
//         case J9BCistore0:
//         case J9BCistore1:
//         case J9BCistore2:
//         case J9BCistore3:
//         case J9BClstore0:
//         case J9BClstore1:
//         case J9BClstore2:
//         case J9BClstore3:
//         case J9BCfstore0:
//         case J9BCfstore1:
//         case J9BCfstore2:
//         case J9BCfstore3:
//         case J9BCdstore0:
//         case J9BCdstore1:
//         case J9BCdstore2:
//         case J9BCdstore3:
//         case J9BCastore0:
//         case J9BCastore1:
//         case J9BCastore2:
//         case J9BCastore3:
//         case J9BCiastore:
//         case J9BClastore:
//         case J9BCfastore:
//         case J9BCdastore:
//         case J9BCaastore:
//         case J9BCbastore:
//         case J9BCcastore:
//         case J9BCsastore:
//         case J9BCpop:
//         case J9BCpop2:
//         case J9BCdup:
//         case J9BCdupx1:
//         case J9BCdupx2:
//         case J9BCdup2:
//         case J9BCdup2x1:
//         case J9BCdup2x2:
//         case J9BCswap:
//         case J9BCiadd:
//         case J9BCladd:
//         case J9BCfadd:
//         case J9BCdadd:
//         case J9BCisub:
//         case J9BClsub:
//         case J9BCfsub:
//         case J9BCdsub:
//         case J9BCimul:
//         case J9BClmul:
//         case J9BCfmul:
//         case J9BCdmul:
//         case J9BCidiv:
//         case J9BCldiv:
//         case J9BCfdiv:
//         case J9BCddiv:
//         case J9BCirem:
//         case J9BClrem:
//         case J9BCfrem:
//         case J9BCdrem:
//         case J9BCineg:
//         case J9BClneg:
//         case J9BCfneg:
//         case J9BCdneg:
//         case J9BCishl:
//         case J9BClshl:
//         case J9BCishr:
//         case J9BClshr:
//         case J9BCiushr:
//         case J9BClushr:
//         case J9BCiand:
//         case J9BCland:
//         case J9BCior:
//         case J9BClor:
//         case J9BCixor:
//         case J9BClxor:
//         case J9BCi2l:
//         case J9BCi2f:
//         case J9BCi2d:
//         case J9BCl2i:
//         case J9BCl2f:
//         case J9BCl2d:
//         case J9BCf2i:
//         case J9BCf2l:
//         case J9BCf2d:
//         case J9BCd2i:
//         case J9BCd2l:
//         case J9BCd2f:
//         case J9BCi2b:
//         case J9BCi2c:
//         case J9BCi2s:
//         case J9BClcmp:
//         case J9BCfcmpl:
//         case J9BCfcmpg:
//         case J9BCdcmpl:
//         case J9BCdcmpg:
//         case J9BCgenericReturn:
//         case J9BCReturnC:
//         case J9BCReturnS:
//         case J9BCReturnB:
//         case J9BCReturnZ:
//         case J9BCarraylength:
//         case J9BCathrow:
//         case J9BCmonitorenter:
//         case J9BCmonitorexit:
//         case J9BCasyncCheck:
//         case J9BCbreakpoint:
//             return 1;
//         case J9BCbipush:
//         case J9BCnewarray:
//         case J9BCaload:
//         case J9BCldc:
//         case J9BCiload:
//         case J9BClload:
//         case J9BCfload:
//         case J9BCdload:
//         case J9BCistore:
//         case J9BClstore:
//         case J9BCfstore:
//         case J9BCdstore:
//         case J9BCastore:
//             return 2;
//         case J9BCsipush:
//         case J9BCldcw:
//         case J9BCldc2lw:
//         case J9BCldc2dw:
//         case J9BCifeq:
//         case J9BCifne:
//         case J9BCiflt:
//         case J9BCifge:
//         case J9BCifgt:
//         case J9BCifle:
//         case J9BCificmpeq:
//         case J9BCificmpne:
//         case J9BCificmplt:
//         case J9BCificmpge:
//         case J9BCificmpgt:
//         case J9BCificmple:
//         case J9BCifacmpeq:
//         case J9BCifacmpne:
//         case J9BCifnull:
//         case J9BCifnonnull:
//         case J9BCgoto:
//         case J9BCgetstatic:
//         case J9BCputstatic:
//         case J9BCgetfield:
//         case J9BCputfield:
//         case J9BCinvokevirtual:
//         case J9BCinvokespecial:
//         case J9BCinvokestatic:
//         case J9BCnew:
//         case J9BCanewarray:
//         case J9BCcheckcast:
//         case J9BCinstanceof:
//         case J9BCiinc:
//             return 3;
//         case J9BCmultianewarray:
//             return 4;
//         case J9BCinvokeinterface:
//         case J9BCinvokedynamic:
//         case J9BCgotow:
//             return 5;
//         case J9BCtableswitch:
//             return calculateTableswitchLength(pc);
//         case J9BClookupswitch:
//             return calculateLookupswitchLength(pc);
//         case J9BCwide:
//             return calculateWideInstructionLength(pc);
//         default:
//             return -1;
//         }
//     }

//     void getAnalyzedMethods()
//     {
//         std::ifstream infile("mi.txt");
//         std::string line;

//         if (!infile)
//         {
//             std::cerr << "Error opening file." << std::endl;
//             return;
//         }

//         while (std::getline(infile, line))
//         {
//             if (!line.empty())
//             {
//                 analysedMethodNames.insert(line);
//             }
//         }

//         infile.close();
//     }
//     // refernce https://en.wikipedia.org/wiki/List_of_Java_bytecode_instructions , https://docs.oracle.com/javase/specs/jvms/se7/html/jvms-6.html
//     void executeBytecode(TR_J9ByteCode bytecode, uint8_t *pc, PointerAssignmentGraph *pag, operandStack *stack, TR_ResolvedMethod *resolvedMethod,
//                          J9Method *currentMethod, int methodIndex, int bci, std::unordered_map<int, PAGNode *> &variableMap, bool hasReturnType, TR::Compilation *comp)
//     {

//         TR_OpaqueMethodBlock *method_block = reinterpret_cast<TR_OpaqueMethodBlock *>(currentMethod);
//         uint16_t cpIndex = (pc[2] << 8) | pc[1];

//         switch (bytecode)
//         {

//         case J9BCnop:
//             break;
//         case J9BCaconstnull:
//         {
//             PAGNode *null_node_ptr;

//             null_node_ptr = new PAGNode(NULL_OBJ, -1, nullptr, method_block, bci, methodIndex);
//             pag->PAG_nodes.insert(null_node_ptr);
//             pag->methods_to_allMethodNodes[methodIndex].push_back(null_node_ptr);

//             pag->methods_to_allMethodNodes[methodIndex].push_back(null_node_ptr);
//             pag->PAG_nodes.insert(null_node_ptr);

//             stack->pushRef(null_node_ptr);
//             break;
//         }

//         // ignore for now since they dont effect PAG
//         case J9BCiconstm1: /*stack->pushInt(-1);*/
//             break;
//         case J9BCiconst0: /*stack->pushInt(0);*/
//             break;
//         case J9BCiconst1: /*stack->pushInt(1);*/
//             break;
//         case J9BCiconst2: /*stack->pushInt(2); */
//             break;
//         case J9BCiconst3: /*stack->pushInt(3);*/
//             break;
//         case J9BCiconst4: /*stack->pushInt(4);*/
//             break;
//         case J9BCiconst5: /*stack->pushInt(5);*/
//             break;

//         case J9BClconst0: /*stack->pushLong(0);*/
//             break;
//         case J9BClconst1: /*stack->pushLong(1);*/
//             break;

//         case J9BCfconst0: /*stack->pushFloat(0.0f);*/
//             break;
//         case J9BCfconst1: /*stack->pushFloat(1.0f); */
//             break;
//         case J9BCfconst2: /*stack->pushFloat(2.0f);*/
//             break;

//         case J9BCdconst0: /*stack->pushDouble(0.0);*/
//             break;
//         case J9BCdconst1: /*stack->pushDouble(1.0);*/
//             break;

//         // iload,lload,dload,fload doesnot effect the PAG so ignore for now
//         case J9BCiload0:
//             break;
//         case J9BCiload1:
//             break;
//         case J9BCiload2:
//             break;
//         case J9BCiload3:
//             break;
//         case J9BClload0:
//             break;
//         case J9BClload1:
//             break;
//         case J9BClload2:
//             break;
//         case J9BClload3:
//             break;
//         case J9BCfload0:
//             break;
//         case J9BCfload1:
//             break;
//         case J9BCfload2:
//             break;
//         case J9BCfload3:
//             break;
//         case J9BCdload0:
//             break;
//         case J9BCdload1:
//             break;
//         case J9BCdload2:
//             break;
//         case J9BCdload3:
//             break;

//         case J9BCaload0:
//         {
//             PAGNode *ref = variableMap[0];
//             stack->pushRef(ref);
//             break;
//         }
//         case J9BCaload1:
//         {
//             PAGNode *ref = variableMap[1];
//             stack->pushRef(ref);
//             break;
//         }
//         case J9BCaload2:
//         {
//             PAGNode *ref = variableMap[2];
//             stack->pushRef(ref);
//             break;
//         }
//         case J9BCaload3:
//         {
//             PAGNode *ref = variableMap[3];
//             stack->pushRef(ref);
//             break;
//         }

//         case J9BCiaload: // load an int from an array
//         case J9BClaload:
//         case J9BCfaload:
//         case J9BCdaload:
//             break;

//         case J9BCaaload: // load a refernce from an array
//         {
//             PAGNode *arrayref = stack->popRef();

//             PAGNode *temp_node_ptr = new PAGNode(VARIABLE, globalIndex, nullptr, method_block, bci, methodIndex);
//             pag->PAG_nodes.insert(temp_node_ptr);
//             pag->methods_to_allMethodNodes[methodIndex].push_back(temp_node_ptr);
//             pag->addEdge(arrayref, temp_node_ptr, GETFIELD, "$");

//             stack->pushRef(temp_node_ptr);
//             break;
//         }

//         case J9BCbaload:
//         case J9BCcaload:
//         case J9BCsaload:
//         case J9BCistore0:
//         case J9BCistore1:
//         case J9BCistore2:
//         case J9BCistore3:
//         case J9BClstore0:
//         case J9BClstore1:
//         case J9BClstore2:
//         case J9BClstore3:
//         case J9BCfstore0:
//         case J9BCfstore1:
//         case J9BCfstore2:
//         case J9BCfstore3:
//         case J9BCdstore0:
//         case J9BCdstore1:
//         case J9BCdstore2:
//         case J9BCdstore3:
//             break;

//         case J9BCastore0:
//         {
//             PAGNode *obj_ref = stack->popRef();
//             if (!variableMap[0])
//             {
//                 variableMap[0] = new PAGNode(VARIABLE, globalIndex, nullptr, method_block, bci, methodIndex);
//                 pag->PAG_nodes.insert(variableMap[0]);
//                 pag->methods_to_allMethodNodes[methodIndex].push_back(variableMap[0]);
//             }
//             pag->addEdge(obj_ref, variableMap[0], ASSIGN, bci);

//             variableMap[0]->pointee_class_names.insert(obj_ref->pointee_class_names.begin(), obj_ref->pointee_class_names.end());

//             break;
//         }
//         case J9BCastore1:
//         {
//             PAGNode *obj_ref = stack->popRef();
//             if (!variableMap[1])
//             {
//                 variableMap[1] = new PAGNode(VARIABLE, globalIndex, nullptr, method_block, bci, methodIndex);
//                 pag->PAG_nodes.insert(variableMap[1]);
//                 pag->methods_to_allMethodNodes[methodIndex].push_back(variableMap[1]);
//             }
//             pag->addEdge(obj_ref, variableMap[1], ASSIGN, bci);

//             variableMap[1]->pointee_class_names.insert(obj_ref->pointee_class_names.begin(), obj_ref->pointee_class_names.end());
//             break;
//         }
//         case J9BCastore2:
//         {
//             PAGNode *obj_ref = stack->popRef();
//             if (!variableMap[2])
//             {
//                 variableMap[2] = new PAGNode(VARIABLE, globalIndex, nullptr, method_block, bci, methodIndex);
//                 pag->PAG_nodes.insert(variableMap[2]);
//                 pag->methods_to_allMethodNodes[methodIndex].push_back(variableMap[2]);
//             }
//             pag->addEdge(obj_ref, variableMap[2], ASSIGN, bci);

//             variableMap[2]->pointee_class_names.insert(obj_ref->pointee_class_names.begin(), obj_ref->pointee_class_names.end());
//             break;
//         }
//         case J9BCastore3:
//         {
//             PAGNode *obj_ref = stack->popRef();
//             if (!variableMap[3])
//             {
//                 variableMap[3] = new PAGNode(VARIABLE, globalIndex, nullptr, method_block, bci, methodIndex);
//                 pag->PAG_nodes.insert(variableMap[3]);
//                 pag->methods_to_allMethodNodes[methodIndex].push_back(variableMap[3]);
//             }
//             pag->addEdge(obj_ref, variableMap[3], ASSIGN, bci);

//             variableMap[3]->pointee_class_names.insert(obj_ref->pointee_class_names.begin(), obj_ref->pointee_class_names.end());
//             break;
//         }

//         // store an int into an array
//         case J9BCiastore:
//             break;
//         case J9BClastore:
//             break;
//         case J9BCfastore:
//             break;
//         case J9BCdastore:
//             break;
//         // store a reference in an array
//         case J9BCaastore:
//         {
//             PAGNode *value = stack->popRef();
//             PAGNode *arrayRef = stack->popRef();

//             pag->addEdge(value, arrayRef, PUTFIELD, "$");

//             // if (pag->threadAccessibleFields.find(fullName) != pag->threadAccessibleFields.end())
//             // {
//             //     pag->LeakyNodes.insert(value);
//             // }
//             updateMatchEdges(pag);

//             break;
//         }
//         case J9BCbastore:
//             break;
//         case J9BCcastore:
//             break;
//         case J9BCsastore:
//             break;

//         case J9BCpop:
//             break;
//         case J9BCpop2:
//             break;

//         case J9BCdup:
//         {
//             StackFrame s = stack->pop();
//             StackFrame s2 = {s.type, s.value};

//             stack->push(s);
//             stack->push(s2);
//             break;
//         }
//         case J9BCdupx1:
//         case J9BCdupx2:
//         case J9BCdup2:
//         case J9BCdup2x1:
//         case J9BCdup2x2:
//             break;

//         case J9BCswap:
//         {
//             StackFrame s = stack->pop();
//             StackFrame s2 = stack->pop();

//             stack->push(s2);
//             stack->push(s);
//             break;
//         }

//         case J9BCiadd:
//         case J9BCladd:
//         case J9BCfadd:
//         case J9BCdadd:
//         case J9BCisub:
//         case J9BClsub:
//         case J9BCfsub:
//         case J9BCdsub:
//         case J9BCimul:
//         case J9BClmul:
//         case J9BCfmul:
//         case J9BCdmul:
//         case J9BCidiv:
//         case J9BCldiv:
//         case J9BCfdiv:
//         case J9BCddiv:
//         case J9BCirem:
//         case J9BClrem:
//         case J9BCfrem:
//         case J9BCdrem:
//         case J9BCineg:
//         case J9BClneg:
//         case J9BCfneg:
//         case J9BCdneg:
//         case J9BCishl:
//         case J9BClshl:
//         case J9BCishr:
//         case J9BClshr:
//         case J9BCiushr:
//         case J9BClushr:
//         case J9BCiand:
//         case J9BCland:
//         case J9BCior:
//         case J9BClor:
//         case J9BCixor:
//         case J9BClxor:
//         case J9BCi2l:
//         case J9BCi2f:
//         case J9BCi2d:
//         case J9BCl2i:
//         case J9BCl2f:
//         case J9BCl2d:
//         case J9BCf2i:
//         case J9BCf2l:
//         case J9BCf2d:
//         case J9BCd2i:
//         case J9BCd2l:
//         case J9BCd2f:
//         case J9BCi2b:
//         case J9BCi2c:
//         case J9BCi2s:
//         case J9BClcmp:
//         case J9BCfcmpl:
//         case J9BCfcmpg:
//         case J9BCdcmpl:
//         case J9BCdcmpg:
//             break;

//         case J9BCgenericReturn:
//         {
//             if (hasReturnType)
//             {

//                 PAGNode *obj_ref = stack->popRef();
//                 PAGNode *return_pag_node_ptr = pag->methodIndex_to_returnNode[methodIndex];
//                 std::cout << methodIndex << " " << return_pag_node_ptr << std::endl;
//                 pag->addEdge(obj_ref, return_pag_node_ptr, ASSIGN);

//                 return_pag_node_ptr->pointee_class_names.insert(obj_ref->pointee_class_names.begin(), obj_ref->pointee_class_names.end());
//             }
//             // else if(stack->size() > 0)
//             //     stack->pop();

//             break;
//         }
//         case J9BCarraylength:
//         case J9BCathrow:
//         case J9BCmonitorenter:
//         case J9BCmonitorexit:
//         case J9BCReturnC:
//         case J9BCReturnS:
//         case J9BCReturnB:
//         case J9BCReturnZ:
//         case J9BCasyncCheck:
//         case J9BCbreakpoint:
//             break;

//         case J9BCbipush:
//         case J9BCnewarray:
//         {
//         }

//         case J9BCsipush:
//         case J9BCiload:
//         case J9BClload:
//         case J9BCfload:
//         case J9BCdload:
//             break;
//         case J9BCaload:
//         {
//             int index = pc[1];
//             PAGNode *ref = variableMap[index];
//             stack->pushRef(ref);
//             break;
//         }
//         case J9BCistore:
//         case J9BClstore:
//         case J9BCfstore:
//         case J9BCdstore:
//             break;

//         case J9BCastore:
//         {
//             PAGNode *obj_ref = stack->popRef();
//             int index = pc[1];
//             std::cout << " " << index;
//             if (!variableMap[index])
//             {
//                 variableMap[index] = new PAGNode(VARIABLE, globalIndex, nullptr, method_block, bci, methodIndex);
//                 pag->PAG_nodes.insert(variableMap[index]);
//                 pag->methods_to_allMethodNodes[methodIndex].push_back(variableMap[index]);
//             }

//             PAGNode *var = variableMap[index];
//             pag->addEdge(obj_ref, var, ASSIGN, bci);

//             var->pointee_class_names.insert(obj_ref->pointee_class_names.begin(), obj_ref->pointee_class_names.end());

//             break;
//         }

//         case J9BCldc:
//         case J9BCldcw:
//         case J9BCifeq:
//         case J9BCifne:
//         case J9BCiflt:
//         case J9BCifge:
//         case J9BCifgt:
//         case J9BCifle:
//         case J9BCificmpeq:
//         case J9BCificmpne:
//         case J9BCificmplt:
//         case J9BCificmpge:
//         case J9BCificmpgt:
//         case J9BCificmple:
//         case J9BCifacmpeq:
//         case J9BCifacmpne:
//         case J9BCifnull:
//         case J9BCifnonnull:
//         case J9BCgoto:
//             break;

//         case J9BCgetstatic:
//         case J9BCgetfield:
//         {

//             J9ConstantPool *cp = J9_CP_FROM_METHOD(currentMethod);
//             J9ROMMethodRef *romMethodRef = (J9ROMMethodRef *)(cp->romConstantPool + cpIndex);
//             U_32 classRefIndex = romMethodRef->classRefCPIndex;
//             J9ROMStringRef *romStringRef = (J9ROMStringRef *)&cp->romConstantPool[classRefIndex];
//             J9UTF8 *classNameWrapper = J9ROMSTRINGREF_UTF8DATA(romStringRef);
//             int classNameLength = J9UTF8_LENGTH(classNameWrapper);
//             char *classNameChars = (char *)J9UTF8_DATA(classNameWrapper);
//             std::string className(classNameChars, classNameLength);

//             int fieldNameLength = 0;
//             const char *fieldNameChars = resolvedMethod->fieldNameChars(cpIndex, fieldNameLength);
//             std::string fieldName(fieldNameChars, fieldNameLength);
//             std::cout << "  -> fieldName= " << fieldName << std::endl;

//             PAGNode *temp_node_ptr = new PAGNode(VARIABLE, globalIndex, nullptr, method_block, bci, methodIndex);
//             pag->PAG_nodes.insert(temp_node_ptr);
//             pag->methods_to_allMethodNodes[methodIndex].push_back(temp_node_ptr);

//             if (bytecode == J9BCgetstatic)
//             {
//                 if (class_to_staticPAGNode.find(className) == class_to_staticPAGNode.end())
//                 {
//                     class_to_staticPAGNode[className] = new PAGNode(STATIC, className, methodIndex);
//                     pag->methods_to_allMethodNodes[methodIndex].push_back(class_to_staticPAGNode[className]);

//                     pag->PAG_nodes.insert(class_to_staticPAGNode[className]);
//                 }

//                 PAGNode *static_pag_ptr = class_to_staticPAGNode[className];
//                 pag->addEdge(static_pag_ptr, temp_node_ptr, GETFIELD, fieldName);
//             }
//             else
//             {
//                 PAGNode *obj_ref = stack->popRef();
//                 pag->addEdge(obj_ref, temp_node_ptr, GETFIELD, fieldName);
//             }

//             stack->pushRef(temp_node_ptr);
//             // update match edges
//             updateMatchEdges(pag);

//             // to get the dynamic type of field
//             for (auto *edge : pag->getMatchEdgesEndingAt(temp_node_ptr))
//             {
//                 PAGNode *src = edge->src;
//                 temp_node_ptr->pointee_class_names.insert(src->pointee_class_names.begin(), src->pointee_class_names.end());
//             }
//             break;
//         }
//         case J9BCputstatic:
//         case J9BCputfield:
//         {
//             J9ConstantPool *cp = J9_CP_FROM_METHOD(currentMethod);
//             J9ROMMethodRef *romMethodRef = (J9ROMMethodRef *)(cp->romConstantPool + cpIndex);
//             U_32 classRefIndex = romMethodRef->classRefCPIndex;
//             J9ROMStringRef *romStringRef = (J9ROMStringRef *)&cp->romConstantPool[classRefIndex];
//             J9UTF8 *classNameWrapper = J9ROMSTRINGREF_UTF8DATA(romStringRef);
//             int classNameLength = J9UTF8_LENGTH(classNameWrapper);
//             char *classNameChars = (char *)J9UTF8_DATA(classNameWrapper);
//             std::string className(classNameChars, classNameLength);

//             int fieldNameLength = 0;
//             const char *fieldNameChars = resolvedMethod->fieldNameChars(cpIndex, fieldNameLength);

//             std::string fieldName(fieldNameChars, fieldNameLength);

//             std::cout << "  ->className in putfield " << className << std::endl;
//             std::cout << "  -> fieldName= " << fieldName << std::endl;
//             std::string fullName = className + "." + fieldName;
//             PAGNode *value = stack->popRef();

//             if (bytecode == J9BCputstatic)
//             {
//                 if (class_to_staticPAGNode.find(className) == class_to_staticPAGNode.end())
//                 {
//                     class_to_staticPAGNode[className] = new PAGNode(STATIC, className, methodIndex);
//                     pag->methods_to_allMethodNodes[methodIndex].push_back(class_to_staticPAGNode[className]);

//                     pag->PAG_nodes.insert(class_to_staticPAGNode[className]);
//                 }

//                 PAGNode *static_pag_ptr = class_to_staticPAGNode[className];
//                 pag->addEdge(value, static_pag_ptr, PUTFIELD, fieldName);
//                 pag->LeakyNodes.insert(value);
//             }
//             else
//             {
//                 PAGNode *obj_ref = stack->popRef();
//                 pag->addEdge(value, obj_ref, PUTFIELD, fieldName);

//                 if (pag->threadAccessibleFields.find(fullName) != pag->threadAccessibleFields.end())
//                 {
//                     pag->LeakyNodes.insert(value);
//                 }

//                 for (std::string classN : obj_ref->pointee_class_names)
//                 {
//                     std::string full_name = classN + "." + fieldName;
//                     value->variableNames.insert(full_name);
//                 }
//             }

//             // update match edges
//             updateMatchEdges(pag);

//             break;
//         }
//             // case J9BCinvokevirtual:
//             // {
//             //     std::cout << "invokevirtual: cpIndex " << static_cast<int>((pc[2] << 8) | pc[1]) << std::endl;
//             //     // J9Method *j9method = jitResolveSpecialMethodRef(((TR_J9VMBase *)comp->fe())->getCurrentVMThread(),
//             //     //                                                 J9_CP_FROM_METHOD(reinterpret_cast<J9Method *>(resolvedMethod)), cpIndex, J9_RESOLVE_FLAG_JIT_COMPILE_TIME);
//             //     J9Method *j9method;
//             //     J9Method *j9Method_resolved = reinterpret_cast<J9Method *>(resolvedMethod);
//             //     J9ConstantPool *cp = J9_CP_FROM_METHOD(j9Method_resolved);
//             //     J9VMThread *j9vm = ((TR_J9VMBase *)comp->fe())->getCurrentVMThread();
//             //     J9RAMSpecialMethodRef *ramSpecialMethodRef = (J9RAMSpecialMethodRef *)&cp[cpIndex];
//             //     J9Method *ramMethod = ramSpecialMethodRef->method;
//             //     TR_ResolvedMethod* res = reinterpret_cast<TR_ResolvedMethod *>(ramMethod);
//             //     // std::cout << "The params slots are: " << res->numberOfParameterSlots() << std::endl;

//             //     break;
//             // }

//         case J9BCinvokedynamic:
//             break;
//         case J9BCinvokestatic:
//         case J9BCinvokeinterface:
//         case J9BCinvokevirtual:
//         case J9BCinvokespecial:
//         {

//             std::cout << "invokespecial/invokevirtual: cpIndex " << cpIndex << std::endl;
//             uint len = 0;
//             J9Method *j9method;

//             J9ConstantPool *cp = J9_CP_FROM_METHOD(currentMethod);
//             J9VMThread *j9vm = ((TR_J9VMBase *)comp->fe())->getCurrentVMThread();
//             J9RAMSpecialMethodRef *ramSpecialMethodRef = (J9RAMSpecialMethodRef *)&cp[cpIndex];

//             J9ROMConstantPoolItem *romCPItem = &(J9_ROM_CP_FROM_CP(J9_CP_FROM_METHOD(currentMethod))[cpIndex]);
//             J9ROMMethodRef *romMethodRef = (J9ROMMethodRef *)romCPItem;
//             J9ROMNameAndSignature *nameAndSig = J9ROMMETHODREF_NAMEANDSIGNATURE(romMethodRef);
//             J9UTF8 *signature_utf8 = J9ROMNAMEANDSIGNATURE_SIGNATURE(nameAndSig);
//             J9UTF8 *name_utf8 = J9ROMNAMEANDSIGNATURE_NAME(nameAndSig);

//             char *sigChars = (char *)J9UTF8_DATA(signature_utf8);
//             U_16 sigLength = J9UTF8_LENGTH(signature_utf8);
//             std::string signature(sigChars, sigLength);

//             char *nameChars = (char *)J9UTF8_DATA(name_utf8);
//             U_16 nameLength = J9UTF8_LENGTH(name_utf8);
//             std::string name(nameChars, nameLength);

//             std::cout << "   -> " << name << signature << " is the method!!!" << std::endl;
//             // methodName along with signature;
//             string methodName = name + signature;

//             vector<PAGNode *> actual_params;
//             // get number of parameters
//             int parameter_count = count_parameters(sigChars);
//             for (int i = parameter_count - 1; i >= 0; i--)
//             {
//                 if (is_reference_type(sigChars, i))
//                 {
//                     actual_params.push_back(stack->popRef());
//                 }
//             }
//             std::reverse(actual_params.begin(), actual_params.end());

//             bool isStatic = (bytecode == J9BCinvokestatic);
//             bool isInterfaceInvoke = (bytecode == J9BCinvokeinterface);
//             int callsiteBCI = bci;

//             if (isStatic)
//             {
//                 J9ConstantPool *cp = J9_CP_FROM_METHOD(currentMethod);
//                 J9ROMMethodRef *romMethodRef = (J9ROMMethodRef *)(cp->romConstantPool + cpIndex);
//                 U_32 classRefIndex = romMethodRef->classRefCPIndex;
//                 J9ROMStringRef *romStringRef = (J9ROMStringRef *)&cp->romConstantPool[classRefIndex];
//                 J9UTF8 *classNameWrapper = J9ROMSTRINGREF_UTF8DATA(romStringRef);
//                 int classNameLength = J9UTF8_LENGTH(classNameWrapper);
//                 char *classNameChars = (char *)J9UTF8_DATA(classNameWrapper);
//                 std::string className(classNameChars, classNameLength);

//                 // U_32 classRefIndex = romMethodRef->classRefCPIndex;
//                 // std::cout << "classRefIndex = " << classRefIndex << std::endl;
//                 // // J9ROMClassRef *romClassRef = (J9ROMClassRef *)(cp + classRefIndex);
//                 // J9ROMConstantPoolItem *romCPItem_class = &(J9_ROM_CP_FROM_CP(J9_CP_FROM_METHOD(currentMethod))[classRefIndex]);

//                 // int32_t classNameLength;
//                 // char *classNameChars = utf8Data(J9ROMCLASSREF_NAME((J9ROMClassRef *)&(((J9ROMConstantPoolItem *)cp->romConstantPool)[classRefIndex])));
//                 // J9ROMConstantPoolItem *romClassCPItem = &(cp->romConstantPool[classRefIndex]);
//                 // J9ROMClassRef *romClassRef = (J9ROMClassRef *)romClassCPItem;

//                 // U_16 nameIndex = romClassRef->name;
//                 // J9ROMConstantPoolItem *classNameUtf8CPItem = &(cp->romConstantPool[nameIndex]);
//                 // J9UTF8 *classNameUtf8 = (J9UTF8 *)classNameUtf8CPItem;

//                 // Now extract as before
//                 // char *classNameChars = (char *)J9UTF8_DATA(classNameUtf8);
//                 // U_16 classNameLength = J9UTF8_LENGTH(classNameUtf8);
//                 // J9ROMStringRef *romStringRef = (J9ROMStringRef *)&cp->romConstantPool[classRefIndex];
//                 // J9UTF8 * classNameWrapper = J9ROMSTRINGREF_UTF8DATA(romStringRef);
//                 // int classNameLength = J9UTF8_LENGTH(classNameWrapper);
//                 // char * classNameChars = (char*) J9UTF8_DATA(classNameWrapper);
//                 // std::string className(classNameChars, classNameLength);
//                 std::cout << "  ->invokestatic className  " << className << std::endl;

//                 bool found = searchForOveridingMethodsInClass(className, name, signature, pag, ((TR_J9VMBase *)comp->fe()), resolvedMethod, actual_params, bci, comp);
//             }
//             else
//             {
//                 PAGNode *receiver_obj_ptr = stack->popRef();

//                 actual_params.insert(actual_params.begin(), receiver_obj_ptr); // (this,arg1,arg2,...)

//                 J9ConstantPool *cp = J9_CP_FROM_METHOD(currentMethod);
//                 J9ROMMethodRef *romMethodRef = (J9ROMMethodRef *)(cp->romConstantPool + cpIndex);
//                 U_32 classRefIndex = romMethodRef->classRefCPIndex;
//                 J9ROMStringRef *romStringRef = (J9ROMStringRef *)&cp->romConstantPool[classRefIndex];
//                 J9UTF8 *classNameWrapper = J9ROMSTRINGREF_UTF8DATA(romStringRef);
//                 int classNameLength = J9UTF8_LENGTH(classNameWrapper);
//                 char *classNameChars = (char *)J9UTF8_DATA(classNameWrapper);
//                 std::string staticClassName(classNameChars, classNameLength);
//                 for (auto className : receiver_obj_ptr->pointee_class_names)
//                 {
//                     if (threadExtendingClasses.find(className) != threadExtendingClasses.end() && name == "start")
//                     {
//                         name = "run";
//                     }

//                     std::string full_name = className + "." + name + signature;
//                     std::string staticName = staticClassName + "." + name + signature;
//                     std::cout << "full_name = " << full_name << "Stt = " << staticName << std::endl;
//                     if (staticName.rfind("java/lang/Object.<init>()") == 0)
//                         break;

//                     if (name.find("java/lang/reflect/Constructor.newInstance([Ljava/lang/Object;)Ljava/lang/Object") != std::string::npos || name.find("java/lang/reflect/Method.invoke(Ljava/lang/Object;[Ljava/lang/Object;)Ljava/lang/Object;") != std::string::npos)
//                     {

//                         TR_OpaqueMethodBlock *method_block = reinterpret_cast<TR_OpaqueMethodBlock *>(currentMethod);
//                         TR_ResolvedMethod *resolved_Method = comp->fe()->createResolvedMethod(comp->trMemory(), method_block, 0);

//                         // int classNameLength = resolvedMethod->classNameLength();
//                         // const char* className = resolvedMethod->classNameChars();
//                         int methodNameLength = resolved_Method->nameLength();
//                         const char *methodName = resolved_Method->nameChars();
//                         int signatureLength = resolved_Method->signatureLength();
//                         const char *callerSignature = resolved_Method->signatureChars();

//                         std::string signature_name(callerSignature, signatureLength);
//                         std::string caller_method_name(methodName, methodNameLength);
//                         std::string full_caller_name = caller_method_name + "." + signature_name;
//                         J9VMThread *vmThread = ((TR_J9VMBase *)comp->fe())->getCurrentVMThread();
//                         J9JavaVM *javaVM = vmThread->javaVM;
//                         int32_t lineNumber = (int32_t)getLineNumberForROMClass(javaVM, currentMethod, bci);
//                         ;

//                         std::unordered_set<std::string> targets = getReflectiveTargets(full_caller_name, lineNumber);
//                         for (std::string fullName : targets)
//                         {
//                             auto dotPos = fullName.find('.');
//                             auto parenPos = fullName.find('(');

//                             className = fullName.substr(0, dotPos);
//                             name = fullName.substr(dotPos + 1, parenPos - dotPos - 1) + "." + fullName.substr(parenPos);
//                         }
//                     }

//                     bool found = searchForOveridingMethodsInClass(className, name, signature, pag, ((TR_J9VMBase *)comp->fe()), resolvedMethod, actual_params, bci, comp);
//                     if (!found)
//                     {
//                         bool found_in_superClass = false;

//                         TR_OpaqueClassBlock *type = comp->fe()->getClassFromSignature(className.c_str(), className.length(), comp->getCurrentMethod(), true);
//                         J9Class **superClasses = TR::Compiler->cls.superClassesOf(type);
//                         int classDepth = TR::Compiler->cls.classDepthOf(type);

//                         for (int i = classDepth - 1; i >= 0; i--)
//                         {
//                             J9UTF8 *superClassName_utf8 = J9ROMCLASS_CLASSNAME(superClasses[i]->romClass);
//                             char *name_chars = (char *)J9UTF8_DATA(superClassName_utf8);
//                             std::string superClassName(name_chars, superClassName_utf8->length);

//                             found = searchForOveridingMethodsInClass(superClassName, name, signature, pag, ((TR_J9VMBase *)comp->fe()), resolvedMethod, actual_params, bci, comp);
//                             if (found)
//                                 break;
//                         }
//                     }

//                     if (!found)
//                     {
//                         /*check if there is exactly one maximally-specific method
//                         (§5.4.3.3) in the superinterfaces of C that matches the resolved
//                         method's name and descriptor and is not abstract, then it is
//                         the method to be invoked.*/
//                     }
//                 }
//             }

//             break;
//         }

//         case J9BCanewarray:
//         case J9BCnew:
//         {
//             uint32_t classNamelength = 0;
//             char *classNameChars = resolvedMethod->getClassNameFromConstantPool(cpIndex, classNamelength);
//             std::string className(classNameChars, classNamelength);
//             std::cout << "  -> Create an object of type: " << className << std::endl;

//             PAGNode *obj_ptr = new PAGNode(OBJECT, -1, nullptr, method_block, bci, methodIndex);
//             pag->PAG_nodes.insert(obj_ptr);
//             pag->methods_to_allMethodNodes[methodIndex].push_back(obj_ptr);

//             stack->pushRef(obj_ptr);

//             obj_ptr->pointee_class_names.insert(className);
//             break;
//         }

//         case J9BCcheckcast:
//             break;
//         case J9BCinstanceof:
//             break;
//         case J9BCiinc:
//             break;
//         case J9BCldc2lw:
//             break;
//         case J9BCldc2dw:
//             break;

//         case J9BCmultianewarray:
//             break;

//         case J9BCgotow:
//             break;

//         case J9BCtableswitch:
//             break;
//             // case J9BClookupswitch:
//             //     // These require parsing the actual instruction data
//             //     return calculateVariableLengthInstruction(bytecode, pc);

//             // // Wide instructions - depend on the following instruction
//             // case J9BCwide:
//             //     return calculateWideInstructionLength(pc);

//         default:
//             // Safe fallback
//             break;
//         }
//     }

//     bool searchForOveridingMethodsInClass(std::string className, std::string method_name, std::string method_signature, PointerAssignmentGraph *pag, TR_J9VMBase *fej9, TR_ResolvedMethod *resolvedMethod, vector<PAGNode *> actual_params, int bci, TR::Compilation *comp)
//     {
//         TR_OpaqueClassBlock *clazz = fej9->getClassFromSignature(className.c_str(), className.length(), resolvedMethod, true);
//         J9Class *j9Class = (J9Class *)clazz;
//         J9ROMClass *romClass = j9Class->romClass;
//         J9ROMMethod *romMethod = J9ROMCLASS_ROMMETHODS(romClass);

//         for (U_32 i = 0; i < romClass->romMethodCount; i++)
//         {
//             J9Method *ramMethod = &j9Class->ramMethods[i];
//             // std::cout << "Method added is: " ;
//             TR_OpaqueMethodBlock *method_block = reinterpret_cast<TR_OpaqueMethodBlock *>(ramMethod);
//             TR_ResolvedMethod *resolved_Method = comp->fe()->createResolvedMethod(comp->trMemory(), method_block, 0);

//             // int classNameLength = resolvedMethod->classNameLength();
//             // const char* className = resolvedMethod->classNameChars();
//             int methodNameLength = resolved_Method->nameLength();
//             const char *methodName = resolved_Method->nameChars();
//             int signatureLength = resolved_Method->signatureLength();
//             const char *signature = resolved_Method->signatureChars();

//             std::string signature_name(signature, signatureLength);
//             std::string target_method_name(methodName, methodNameLength);
//             std::string full_method_name = className + "." + method_name + method_signature;
//             if (method_signature == signature_name && method_name == target_method_name)
//             {   
//                  vector<PAGNode *> f_params = pag->getFormalParameterNodes(getOrInsertMethodIndex(full_method_name, pag));
//                 if(isLibraryMethod(full_method_name))
//                 {   
//                     for (int f_ind = 0; f_ind < f_params.size(); f_ind++)
//                         f_params[f_ind] = pag->bottom_node;
//                 }
//                 if (analysedMethodNames.find(full_method_name) != analysedMethodNames.end() && changedMethodNames.find(full_method_name) == changedMethodNames.end())
//                 {
//                     for (int f_ind = 0; f_ind < f_params.size(); f_ind++)
//                     {
//                         pag->addEdge(actual_params[f_ind], f_params[f_ind], ASSIGN, bci);
//                     }
//                 }
//                 else // if (changedMethodNames.find(full_method_name) == changedMethodNames.end())
//                 {
//                     traverse_bytecode(ramMethod, pag, getOrInsertMethodIndex(full_method_name, pag), comp);
//                 }
//                 return true;
//             }

//             // std::cout << std::string(className, classNameLength)
//             //         << "." << std::string(methodName, methodNameLength)
//             //         << std::string(signature, signatureLength) << std::endl;
//         }

//         return false;
//     }

//     int count_parameters(const char *signature)
//     {
//         int count = 0;
//         const char *p = strchr(signature, '(') + 1;
//         while (*p && *p != ')')
//         {
//             switch (*p)
//             {
//             case 'B':
//             case 'C':
//             case 'D':
//             case 'F':
//             case 'I':
//             case 'J':
//             case 'S':
//             case 'Z':
//                 ++count;
//                 ++p;
//                 break;
//             case 'L':
//                 ++count;
//                 p = strchr(p, ';') + 1;
//                 break;
//             case '[':
//                 while (*p == '[')
//                     ++p;
//                 if (*p == 'L')
//                     p = strchr(p, ';') + 1;
//                 else
//                     ++p;
//                 ++count;
//                 break;
//             default:
//                 ++p;
//             }
//         }
//         return count;
//     }

    bool is_reference_type(const char *signature, int argumentIndex)
    {
        int idx = 0;
        // std::cout << "Argument index is : " << argumentIndex << std::endl;
        const char *p = strchr(signature, '(') + 1;
        while (*p && *p != ')')
        {

            if (idx == argumentIndex)
            {
                if (*p == 'L')
                {
                    // Object reference
                    return true;
                }
                if (*p == '[')
                {

                    return true;
                }

                return false;
            }

            if (*p == 'L')
            {
                p = strchr(p, ';') + 1;
            }
            else if (*p == '[')
            {

                while (*p == '[')
                    ++p;
                if (*p == 'L')
                {
                    p = strchr(p, ';') + 1;
                }
                else
                {
                    ++p;
                }
            }
            else
            {
                ++p;
            }
            ++idx;
        }
        return false;
    }

    void updateMatchEdges(PointerAssignmentGraph *pag)
    {
        for (PAGEdge *e1 : pag->getStoreEdges())
        {
            for (PAGEdge *e2 : pag->getLoadEdges())
            {
                if (e1->field == e2->field)
                {
                    bool exists = false;
                    for (PAGEdge *outEdge : e1->src->outgoing)
                    {
                        if (outEdge->dest == e2->dest && outEdge->type == MATCH)
                        {
                            exists = true;
                            break;
                        }
                    }
                    if (!exists)
                    {
                        pag->addEdge(e1->src, e2->dest, MATCH);
                    }
                }
            }
        }
    }

    void getall_loaded_classes(TR::Compilation *comp)
    {
        // std::cout << "All the loaded classes are: " << std::endl;
        J9VMThread *vmThread = ((TR_J9VMBase *)comp->fe())->getCurrentVMThread();
        J9JavaVM *javaVM = vmThread->javaVM;
        TR::VMAccessCriticalSection criticalSection(comp);

        J9ClassLoader *classLoader = NULL;
        GC_PoolIterator classLoaderIterator(javaVM->classLoaderBlocks);
        while (NULL != (classLoader = (J9ClassLoader *)classLoaderIterator.nextSlot()))
        {
            J9HashTableState walkState;
            J9Class *clazz = javaVM->internalVMFunctions->hashClassTableStartDo(classLoader, &walkState, 0);
            while (clazz)
            {
                if (!J9ROMCLASS_IS_ARRAY(clazz->romClass))
                {
                    // std::string className1 = TR::Compiler->cls.classSignature(comp, reinterpret_cast<TR_OpaqueClassBlock *>(clazz), comp->trMemory());
                    // TR_ASSERT_FATAL(className.size() != 0, "unable to get class name for type");

                    J9Class *j9clazz = (J9Class *)clazz;
                    J9UTF8 *nameUTF8 = J9ROMCLASS_CLASSNAME(j9clazz->romClass);
                    std::string className((char *)J9UTF8_DATA(nameUTF8), J9UTF8_LENGTH(nameUTF8));

                    if (!(className.rfind("java/") == 0 || className.rfind("sun") == 0 || className.rfind("jdk") == 0 || className.rfind("openj9") == 0 || className.rfind("com") == 0))
                    {
                        //    std :: cout << className <<std::endl;
                        all_loaded_classes.insert(className);
                        className_to_fields[className] = getClassFields(clazz, comp->j9VMThread());
                    }
                }
                clazz = javaVM->internalVMFunctions->hashClassTableNextDo(&walkState);
            }
        }
        ////
    }

    void getThreadRelatedClasses(TR::Compilation *comp)
    {
        for (std::string class_name : all_loaded_classes)
        {

            TR_OpaqueClassBlock *type = comp->fe()->getClassFromSignature(class_name.c_str(), class_name.length(), comp->getCurrentMethod(), true);
            J9Class **superClasses = TR::Compiler->cls.superClassesOf(type);

            int classDepth = TR::Compiler->cls.classDepthOf(type);
            // printf("Superclasses of %s:\n", TR::Compiler->cls.classSignature(comp, type, comp->trMemory()));

            // ignore java/lang/Object (at index i=0)
            for (int32_t i = 1; i < classDepth; ++i)
            {
                J9Class *superClass = superClasses[i];
                // CHA[(TR_OpaqueClassBlock *)superClass].insert(type);

                std::string superClassName = TR::Compiler->cls.classSignature(comp, (TR_OpaqueClassBlock *)superClass, comp->trMemory());
                if (superClassName.rfind("Ljava/lang/Thread;") == 0)
                {
                    threadExtendingClasses.insert(class_name);
                }
            }

            std::string tpName = TR::Compiler->cls.classSignature(comp, type, comp->trMemory());
            // std::cout<< "tpName: "<<tpName<<std::endl;
            for (J9ITable *iTableCur = TR::Compiler->cls.iTableOf(type); iTableCur; iTableCur = iTableCur->next)
            {
                // CHA[(TR_OpaqueClassBlock *)iTableCur->interfaceClass].insert(type);
                // std::cout << TR::Compiler->cls.classSignature(comp, (TR_OpaqueClassBlock *)iTableCur->interfaceClass, comp->trMemory()) << "---->" << TR::Compiler->cls.classSignature(comp, type, comp->trMemory()) << std::endl;
                std::string superClassName = TR::Compiler->cls.classSignature(comp, (TR_OpaqueClassBlock *)iTableCur->interfaceClass, comp->trMemory());
                if (superClassName.rfind("Ljava/lang/Runnable") == 0)
                {
                    threadExtendingClasses.insert(class_name);
                }
            }
        }
    }
};