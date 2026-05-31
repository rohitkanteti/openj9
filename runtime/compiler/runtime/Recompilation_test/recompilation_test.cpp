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
#include <chrono>
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
#define D_PREFIX "[DEBUG-RELO] "

#define STATIC_FIELD_READ -10866 // unique negative code for static field read.
#define RETURN_NODE_NAME -56765  // UNIQUE NAME for return node

int globalIndex = 0;
extern TR_ResolvedMethod *getCachedResolvedMethodFromPtr(TR::Compilation *comp, TR_OpaqueMethodBlock *methodPtr);
extern const char *getBytecodeString(TR_J9ByteCode bytecode);
extern bool returnsObject(const std::string &methodSignature, std::string &returnStaticType);
extern bool isLibraryMethod(std::string methodName);
extern int count_parameters(const char *signature);
extern bool isUnconditionalBranch(TR_J9ByteCode bc);
extern int getSlotForArgument(const char *descriptor, int argIndex);
extern std::string getParameterReferenceType(const char *signature, int parameterIndex);
extern int32_t getInstructionLength(TR_J9ByteCode bytecode, uint8_t *pc);
extern int32_t branchTarget(int32_t pcIndex, TR_J9ByteCode bc, uint8_t *pc);
extern vector<int> switchTargets(int32_t pcIndex, TR_J9ByteCode bc, uint8_t *pc);
extern bool isReturnOrThrow(TR_J9ByteCode bc);
extern bool isBranch(TR_J9ByteCode bc);
extern bool isSwitch(TR_J9ByteCode bc);
extern void executeBytecode(TR_J9ByteCode bytecode, uint8_t *pc, PointerAssignmentGraph *pag, operandStack *stack, TR_ResolvedMethod *resolvedMethod,
                            J9Method *currentMethod, int methodIndex, int bci, std::unordered_map<int, PAGNode *> &variableMap, bool hasReturnType, TR::Compilation *comp, J9Class *J9currentClass, PAGNode *primitive_node, PAGNode *comp_type_2,std::string);

void traverse_cfg(J9Method *method, PointerAssignmentGraph *pag, int methodIndex, TR::Compilation *comp, PAGNode *primitive_node, PAGNode *comp_type2_primitiveNode);
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

struct Block
{
    int32_t id;       // Replaces block->getNumber()
    int32_t startBCI; // Replaces block->getEntry()->getNode()->getByteCodeIndex()
    int32_t endBCI;

    std::vector<Block *> succs;
    std::vector<Block *> preds;

    Block(int id, int32_t start) : id(id), startBCI(start), endBCI(-1) {}
};

struct CFG
{
    Block *entry;
    std::vector<Block *> allBlocks;

    void addNode(Block *b)
    {
        allBlocks.push_back(b);
    }

    void addEdge(Block *from, Block *to)
    {
        from->succs.push_back(to);
        to->preds.push_back(from);
    }
};
static std::unordered_map<std::string, std::vector<CallInfo>> reflectiveCallGraph;
static unordered_set<std::string> all_loaded_classes;
static bool threadClassesIdentified = false;
std::unordered_set<std::string> changedMethodNames;

PointerAssignmentGraph *pag_to_use = nullptr;

CFG *buildCFG(TR_OpaqueMethodBlock *method_block, TR::Compilation *comp, std::map<int32_t, Block *> &blocks, Block *&entryBlock)
{
    int32_t methodSize = TR::Compiler->mtd.bytecodeSize(method_block);
    uintptr_t methodStart = TR::Compiler->mtd.bytecodeStart(method_block);

    CFG *cfg = new CFG();
    std::set<int32_t> leaders;

    leaders.insert(0); // entry always a leader

    // Scan bytecodes to identify leaders
    for (int32_t pcIndex = 0; pcIndex < methodSize;)
    {
        uint8_t *pc = (uint8_t *)(methodStart + pcIndex);
        TR_J9ByteCode bc = TR_J9ByteCodeIterator::convertOpCodeToByteCodeEnum(*pc);
        int32_t len = getInstructionLength(bc, pc);

        if (isBranch(bc))
        {
            int32_t tgt = branchTarget(pcIndex, bc, pc);
            leaders.insert(tgt);
            leaders.insert(pcIndex + len);
        }
        else if (isSwitch(bc))
        {
            auto tgts = switchTargets(pcIndex, bc, pc);
            for (auto t : tgts)
                leaders.insert(t);
            leaders.insert(pcIndex + len);
        }
        else if (isReturnOrThrow(bc))
        {
            leaders.insert(pcIndex + len);
        }

        pcIndex += len;
    }

    int blockID = 0;
    for (int32_t leader : leaders)
    {
        Block *b = new Block(blockID++, leader);
        blocks[leader] = b;
        cfg->addNode(b);
    }

    std::vector<int32_t> leaderVec(leaders.begin(), leaders.end());
    sort(leaderVec.begin(), leaderVec.end());

    // Add edges between blocks
    for (size_t i = 0; i < leaderVec.size(); i++)
    {
        int32_t start = leaderVec[i];
        Block *block = blocks[start];

        // Find the end of this block (i.e. next leader or method end)
        int32_t end = (i + 1 < leaderVec.size()) ? leaderVec[i + 1] : methodSize;
        block->endBCI = end;

        // Find the last instruction in this block
        int32_t lastInstrStart = start;
        TR_J9ByteCode lastBc = J9BCnop;

        for (int32_t pcIndex = start; pcIndex < end;)
        {
            uint8_t *pc = (uint8_t *)(methodStart + pcIndex);
            TR_J9ByteCode bc = TR_J9ByteCodeIterator::convertOpCodeToByteCodeEnum(*pc);
            int32_t len = getInstructionLength(bc, pc);

            lastInstrStart = pcIndex;
            lastBc = bc;

            pcIndex += len;
            if (pcIndex >= end)
                break;
        }

        uint8_t *lastPc = (uint8_t *)(methodStart + lastInstrStart);

        // Add edges based on the last instruction of the block
        if (isBranch(lastBc))
        {
            int tgt = branchTarget(lastInstrStart, lastBc, lastPc);
            if (blocks.count(tgt))
                cfg->addEdge(block, blocks[tgt]);

            if (!isUnconditionalBranch(lastBc) && blocks.count(end))
                cfg->addEdge(block, blocks[end]);
        }
        else if (isSwitch(lastBc))
        {
            auto tgts = switchTargets(lastInstrStart, lastBc, lastPc);
            for (auto t : tgts)
            {
                if (blocks.count(t))
                    cfg->addEdge(block, blocks[t]);
            }
        }
        else if (!isReturnOrThrow(lastBc))
        {
            if (blocks.count(end))
                cfg->addEdge(block, blocks[end]);
        }
    }

    entryBlock = blocks[0];
    cfg->entry = entryBlock;

    return cfg;
}

class recompilation_test
{
public:
    TR_RelocationRuntime *reloRuntime;

    std::unordered_set<std::string> get_types(PAGNode* v, PointerAssignmentGraph *p) {
        std::unordered_set<std::string> types;
        for (PAGNode* obj : p->points_to(v)) {
            if (obj->type == NEW) {
                if (!obj->comp_type.empty() && obj->comp_type != "type1" && obj->comp_type != "COMP_TYPE_2") {
                    types.insert(obj->comp_type);
                } else if (!obj->class_name.empty()) {
                    types.insert(obj->class_name);
                } else if (!obj->static_type.empty()) {
                    types.insert(obj->static_type);
                }
            }
        }
        return types;
    }

    bool check_pa_inlining(int mx, PointerAssignmentGraph *p_prime, const std::unordered_map<std::string, std::unordered_set<std::string>>& old_callsite_types) {
        for (const auto& pair : old_callsite_types) {
            const std::string& callsite_key = pair.first;
            const std::unordered_set<std::string>& old_types = pair.second;
            
            auto it = p_prime->CG.callsiteParams.find(callsite_key);
            if (it == p_prime->CG.callsiteParams.end() || it->second.empty()) continue;
            PAGNode* receiver = it->second[0];
            
            std::unordered_set<std::string> new_types = get_types(receiver, p_prime);
            
            if (old_types.size() == 1 && (new_types.size() > 1 || old_types != new_types)) {
                return true; 
            }
            
            if (old_types.size() > 1 && new_types.size() == 1) {
                return true; 
            }
        }
        return false;
    }

    int getOrInsertMethodIndex(std::string methodName, PointerAssignmentGraph *pag)
    {
        if (pag->_methodIndices.find(methodName) != pag->_methodIndices.end())
        {
            return pag->_methodIndices[methodName];
        }

        int index = pag->_methodIndices.size() + 1;
        pag->_methodIndices[methodName] = index;
        return index;
    }

    PointerAssignmentGraph *update_PAG(PointerAssignmentGraph *p, int my, J9Method *my_prime_J9Method, CallGraph *CG, string my_full_name)
    {
        // auto start = std::chrono::high_resolution_clock::now();
        if (all_loaded_classes.empty())
        {
            getall_loaded_classes(reloRuntime->comp());
        }
        // auto end = std::chrono::high_resolution_clock::now();
        // auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start).count();
        // std::cout << D_PREFIX << "Time taken to get all loaded classes in update_PAG: " << duration << "  microseconds\n" << std::endl;
        // std::cout.flush();

        // start = std::chrono::high_resolution_clock::now();
        if (!threadClassesIdentified)
        {
            threadClassesIdentified = true;
            getResolvedReflectiveCalls();
            std::ifstream inFile("threadRelatedClasses.txt");
            std::string line;

            if (inFile.is_open())
            {
                threadExtendingClasses.clear();
                while (std::getline(inFile, line))
                {
                    if (!line.empty())
                    {
                        threadExtendingClasses.insert(line);
                    }
                }
                inFile.close();
            }
            else
            {
                TR_ASSERT_FATAL(1, "could not open the file threadRelatedClasses.txt");
            }
        }
        // end = std::chrono::high_resolution_clock::now();
        // duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start).count();
        // std::cout << D_PREFIX << "Time taken to get thread related classes in update_PAG: " << duration << "  microseconds\n" << std::endl;
        // std::cout.flush();

        // start = std::chrono::high_resolution_clock::now();
        for (PAGNode *f_param : p->getFormalParameterNodes(my))
        {
            p->removeAllEdgesFrom(f_param);
        }
        // end = std::chrono::high_resolution_clock::now();
        // duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start).count();
        // std::cout << D_PREFIX << "Time taken to remove edges from formal parameter nodes in update_PAG: " << duration << "  microseconds\n" << std::endl;
        // std::cout.flush();

        // start = std::chrono::high_resolution_clock::now();
        p->removeEdges(my);
        // end = std::chrono::high_resolution_clock::now();
        // duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start).count();
        // std::cout << D_PREFIX << "Time taken to remove edges in update_PAG: " << duration << "  microseconds\n" << std::endl;
        // std::cout.flush();

        // start = std::chrono::high_resolution_clock::now();
        p->removeNodes(my);
        // end = std::chrono::high_resolution_clock::now();
        // duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start).count();
        // std::cout << D_PREFIX << "Time taken to remove nodes in update_PAG: " << duration << "  microseconds\n" << std::endl;
        // std::cout.flush();

        TR::Compilation *comp = reloRuntime->comp();

        PAGNode *comp_type_2 = new PAGNode();
        comp_type_2->static_type = "COMP_TYPE_2";
        comp_type_2->comp_type = "COMP_TYPE_2";

        // start = std::chrono::high_resolution_clock::now();

        traverse_cfg(my_prime_J9Method, p, my, comp, new PAGNode(), comp_type_2);

        // end = std::chrono::high_resolution_clock::now();
        // duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start).count();
        // std::cout << D_PREFIX << "Time taken to traverse PAG in update_PAG: " << duration << "  microseconds\n" << std::endl;
        // std::cout.flush();
        return p;
    }
    std::unordered_set<std::string> get_fields(PointerAssignmentGraph *p, PAGNode *obj)
    {
        std::unordered_set<string> fields;
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

    bool REACH(PAGNode *target_obj, PAGNode *start_node, PointerAssignmentGraph *p)
    {
        const auto &objs = p->points_to(start_node);
        if (objs.find(target_obj) != objs.end())
            return true;

        std::unordered_set<PAGNode *> visited;
        std::queue<PAGNode *> queue;

        queue.push(start_node);
        visited.insert(start_node);

        while (!queue.empty())
        {
            PAGNode *current_node = queue.front();
            queue.pop();

            for (const std::string &field : p->get_fields(current_node))
            {
                const auto &next_nodes = p->get_field_target(current_node, field);

                for (PAGNode *next_node : next_nodes)
                {
                    if (visited.insert(next_node).second)
                    {
                        const auto &pts_set = p->points_to(next_node);
                        if (pts_set.find(target_obj) != pts_set.end())
                        {
                            return true;
                        }

                        queue.push(next_node);
                    }
                }
            }
        }

        return false;
    }

    bool should_recompile(int mx, PointerAssignmentGraph *p_prime, const std::unordered_set<PAGEdge *> &old_allocated_edges, const std::unordered_set<PAGNode *> &old_escaping_objects)
    {
        auto leaky_nodes = p_prime->getLeakyNodes();

        for (PAGEdge *alloc_edge : old_allocated_edges)
        {
            PAGNode *o = alloc_edge->src;

            // Fast O(1) hash lookup
            bool isEscaping = old_escaping_objects.find(o) != old_escaping_objects.end();

            if (isEscaping)
            {
                bool isReachable = false;
                for (PAGNode *u : leaky_nodes)
                {
                    // auto start = std::chrono::high_resolution_clock::now();
                    bool isReach = REACH(o, u, p_prime);
                    // auto end = std::chrono::high_resolution_clock::now();
                    // auto elapsed_update = std::chrono::duration_cast<std::chrono::microseconds>(end - start);
                    // std::cout <<D_PREFIX << "Time for method REACH-1 "<< elapsed_update.count() << " microsecs\n";
                    // std::cout.flush();
                    isReachable |= isReach;
                    if (isReachable)
                        break; // Early exit avoids unnecessary traversals
                }

                if (!isReachable)
                    return true; // Recompile mx
            }
            else
            {
                for (PAGNode *u : leaky_nodes)
                {
                    // auto start = std::chrono::high_resolution_clock::now();
                    bool isReach = REACH(o, u, p_prime);
                    // auto end = std::chrono::high_resolution_clock::now();
                    // auto elapsed_update = std::chrono::duration_cast<std::chrono::microseconds>(end - start);
                    // std::cout <<D_PREFIX << "Time for method REACH-2 "<< elapsed_update.count() << " microsecs\n";
                    // std::cout.flush();
                    if (isReach)
                    {
                        return true; // Recompile mx
                    }
                }
            }
        }
        return false;
    }

    bool is_reference_type(const char *signature, int argumentIndex)
    {
        int idx = 0;
        const char *p = strchr(signature, '(') + 1;
        while (*p && *p != ')')
        {
            if (idx == argumentIndex)
            {
                if (*p == 'L')
                    return true;
                if (*p == '[')
                    return true;
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
                    p = strchr(p, ';') + 1;
                else
                    ++p;
            }
            else
            {
                ++p;
            }
            ++idx;
        }
        return false;
    }

    // void updateMatchEdges(PointerAssignmentGraph *pag)
    // {
    //     for (PAGEdge *e1 : pag->getStoreEdges())
    //     {
    //         for (PAGEdge *e2 : pag->getLoadEdges())
    //         {
    //             if (e1->field == e2->field)
    //             {
    //                 bool exists = false;
    //                 for (PAGEdge *outEdge : e1->src->outgoing)
    //                 {
    //                     if (outEdge->dest == e2->dest && outEdge->type == MATCH)
    //                     {
    //                         exists = true;
    //                         break;
    //                     }
    //                 }
    //                 if (!exists)
    //                 {
    //                     pag->addEdge(e1->src, e2->dest, MATCH);
    //                 }
    //             }
    //         }
    //     }
    // }

    void updateMatchEdges(PointerAssignmentGraph *pag)
    {
        std::unordered_map<std::string, std::vector<PAGEdge *>> loadsByField;

        for (PAGEdge *e2 : pag->getLoadEdges())
        {
            loadsByField[e2->field].push_back(e2);
        }

        for (PAGEdge *e1 : pag->getStoreEdges())
        {
            auto it = loadsByField.find(e1->field);

            if (it == loadsByField.end())
            {
                continue;
            }

            const std::vector<PAGEdge *> &matchingLoads = it->second;

            // 2. INNER LOOP OPTIMIZATION
            std::unordered_set<decltype(e1->dest)> existingMatchDests;

            for (PAGEdge *outEdge : e1->src->outgoing)
            {
                if (outEdge->type == MATCH)
                {
                    existingMatchDests.insert(outEdge->dest);
                }
            }

            for (PAGEdge *e2 : matchingLoads)
            {
                if (existingMatchDests.find(e2->dest) == existingMatchDests.end())
                {
                    pag->addEdge(e1->src, e2->dest, MATCH);
                    existingMatchDests.insert(e2->dest);
                }
            }
        }
    }
    void getall_loaded_classes(TR::Compilation *comp)
    {
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
                    J9Class *j9clazz = (J9Class *)clazz;
                    J9UTF8 *nameUTF8 = J9ROMCLASS_CLASSNAME(j9clazz->romClass);
                    std::string className((char *)J9UTF8_DATA(nameUTF8), J9UTF8_LENGTH(nameUTF8));

                    if (!(className.rfind("java/") == 0 || className.rfind("sun") == 0 || className.rfind("jdk") == 0 || className.rfind("openj9") == 0 || className.rfind("com") == 0))
                    {
                        all_loaded_classes.insert(className);
                        className_to_fields[className] = getClassFields(clazz, comp->j9VMThread());
                    }
                }
                clazz = javaVM->internalVMFunctions->hashClassTableNextDo(&walkState);
            }
        }
    }

    void getThreadRelatedClasses(TR::Compilation *comp)
    {
        for (std::string class_name : all_loaded_classes)
        {
            TR_OpaqueClassBlock *type = comp->fe()->getClassFromSignature(class_name.c_str(), class_name.length(), comp->getCurrentMethod(), true);
            J9Class **superClasses = TR::Compiler->cls.superClassesOf(type);

            int classDepth = TR::Compiler->cls.classDepthOf(type);
            for (int32_t i = 1; i < classDepth; ++i)
            {
                J9Class *superClass = superClasses[i];
                std::string superClassName = TR::Compiler->cls.classSignature(comp, (TR_OpaqueClassBlock *)superClass, comp->trMemory());
                if (superClassName.rfind("Ljava/lang/Thread;") == 0)
                {
                    threadExtendingClasses.insert(class_name);
                }
            }

            for (J9ITable *iTableCur = TR::Compiler->cls.iTableOf(type); iTableCur; iTableCur = iTableCur->next)
            {
                std::string superClassName = TR::Compiler->cls.classSignature(comp, (TR_OpaqueClassBlock *)iTableCur->interfaceClass, comp->trMemory());
                if (superClassName.rfind("Ljava/lang/Runnable") == 0)
                {
                    threadExtendingClasses.insert(class_name);
                }
            }
        }
    }
    int globalIndex_ = 0;

    void traverse_cfg(J9Method *method, PointerAssignmentGraph *pag, int methodIndex, TR::Compilation *comp, PAGNode *primitive_node, PAGNode *comp_type2_primitiveNode)
    {
        TR_OpaqueMethodBlock *method_block = reinterpret_cast<TR_OpaqueMethodBlock *>(method);
        int32_t methodSize = TR::Compiler->mtd.bytecodeSize(method_block);
        uintptr_t methodStart = TR::Compiler->mtd.bytecodeStart(method_block);
        TR_ResolvedMethod *resolvedMethod = getCachedResolvedMethodFromPtr(comp, method_block);

        std::map<int32_t, Block *> blocks;
        Block *entryBlock = nullptr;

        J9ROMMethod *romMethod = J9_ROM_METHOD_FROM_RAM_METHOD(method);
        J9Class *clazz = J9_CLASS_FROM_CP(J9_CP_FROM_METHOD(method));
        J9ROMClass *romClass = clazz->romClass;

        J9UTF8 *utfMethodName = J9ROMMETHOD_NAME(romMethod);
        char *methodName = (char *)J9UTF8_DATA(utfMethodName);
        int32_t methodNameLength = J9UTF8_LENGTH(utfMethodName);

        J9UTF8 *utfSignature = J9ROMMETHOD_SIGNATURE(romMethod);
        char *methodSignature = (char *)J9UTF8_DATA(utfSignature);
        int32_t methodSignatureLength = J9UTF8_LENGTH(utfSignature);

        J9UTF8 *utfClassName = J9ROMCLASS_CLASSNAME(romClass);
        char *classNameChars = (char *)J9UTF8_DATA(utfClassName);
        int32_t classNameLength = J9UTF8_LENGTH(utfClassName);

        std::string name(methodName, methodNameLength);
        std::string className(classNameChars, classNameLength);
        std::string signature(methodSignature, methodSignatureLength);
        std::string returnStaticType;

        bool hasReturnType = returnsObject(methodSignature, returnStaticType);

        int num_params = count_parameters(methodSignature);
        std::unordered_map<int, PAGNode *> variableMap;
        int reference_params = 0;
        if ((romMethod->modifiers & J9AccStatic) == 0)
        {
            reference_params++;
        }

        for (int i = 0; i < num_params; i++)
        {
            if (is_reference_type(methodSignature, i))
            {
                reference_params++;
            }
        }
        std::string fullNAME = className + "." + name + signature;
        if (analysedMethodNames.find(fullNAME) == analysedMethodNames.end())
        {
            bool static_node_created_here = false;
            if ((romMethod->modifiers & J9AccStatic) == 0)
            {
                PAGNode *param_node_ptr = new PAGNode(VARIABLE, 0, nullptr, method_block, -1, methodIndex, className);
                if (pag->methodIndex_to_formalNodes.find(methodIndex) == pag->methodIndex_to_formalNodes.end())
                {
                    static_node_created_here = true;
                    pag->methodIndex_to_allMethodNodes[methodIndex].push_back(param_node_ptr);
                    pag->PAG_nodes.insert(param_node_ptr);
                    pag->methodIndex_to_formalNodes[methodIndex].push_back(param_node_ptr);
                }
            }

            if (static_node_created_here || pag->methodIndex_to_formalNodes.find(methodIndex) == pag->methodIndex_to_formalNodes.end())
            {

                for (int i = 0; i < num_params; i++)
                {

                    if (is_reference_type(methodSignature, i))
                    {
                        int slot_num = getSlotForArgument(methodSignature, i);
                        std::string static_type = getParameterReferenceType(methodSignature, i);

                        PAGNode *param_node_ptr = new PAGNode(VARIABLE, slot_num, nullptr, method_block, -1, methodIndex, static_type);
                        pag->methodIndex_to_allMethodNodes[methodIndex].push_back(param_node_ptr);
                        pag->PAG_nodes.insert(param_node_ptr);
                        pag->methodIndex_to_formalNodes[methodIndex].push_back(param_node_ptr);
                    }
                }
            }
            if (hasReturnType && (pag->methodIndex_to_returnNode.find(methodIndex) == pag->methodIndex_to_returnNode.end()))
            {
                pag->methodIndex_to_returnNode[methodIndex] = new PAGNode(RETURN, RETURN_NODE_NAME, NULL, method_block, -1, methodIndex);
                pag->methodIndex_to_returnNode[methodIndex]->static_type = returnStaticType;
                pag->PAG_nodes.insert(pag->methodIndex_to_returnNode[methodIndex]);
                pag->methodIndex_to_allMethodNodes[methodIndex].push_back(pag->methodIndex_to_returnNode[methodIndex]);
            }
        }
        vector<PAGNode *> formal_param_nodes = pag->methodIndex_to_formalNodes[methodIndex];
        PAGNode *returnNode = nullptr;
        auto it = pag->methodIndex_to_returnNode.find(methodIndex);
        if (it != pag->methodIndex_to_returnNode.end())
        {
            returnNode = it->second;
        }

        if (reference_params != formal_param_nodes.size())
        {
            TR_ASSERT_FATAL(0, "There is a mismatch in the size of paramters maybe the method signature changed.");
        }

        for (int i = 0; i < reference_params; i++)
        {
            if ((romMethod->modifiers & J9AccStatic) != 0)
                variableMap[(formal_param_nodes[i]->name) - 1] = formal_param_nodes[i];
            else
                variableMap[formal_param_nodes[i]->name] = formal_param_nodes[i]; // non-static methods, slot 0 -> this
        }

        int32_t currentIndex = 0;
        int statementCount = 0;
        operandStack *stack = new operandStack();

        // auto start = std::chrono::high_resolution_clock::now();

        // build CFG
        CFG *cfg = buildCFG(method_block, comp, blocks, entryBlock);

        // auto end = std::chrono::high_resolution_clock::now();
        // auto elapsed_update = std::chrono::duration_cast<std::chrono::microseconds>(end - start);
        // std::cout <<D_PREFIX << "Time buildCFG in recompilation_test = "<< elapsed_update.count() << " microsecs\n";
        // std::cout.flush();

        std::unordered_map<Block *, operandStack *> inStacks;
        std::queue<Block *> worklist;

        inStacks[entryBlock] = new operandStack();
        worklist.push(entryBlock);

        J9Class *currentClass = J9_CLASS_FROM_METHOD(method);

        unordered_set<int> worklist_bb_bci;
        worklist_bb_bci.insert(entryBlock->startBCI);

        // start = std::chrono::high_resolution_clock::now();
        while (!worklist.empty())
        {
            Block *bb = worklist.front();
            worklist.pop();

            operandStack *stack = new operandStack(*inStacks[bb]);

            int pcIndex = bb->startBCI;
            worklist_bb_bci.erase(pcIndex);

            while (pcIndex < bb->endBCI)
            {
                uint8_t *pc = (uint8_t *)(methodStart + pcIndex);

                TR_J9ByteCode bytecode = TR_J9ByteCodeIterator::convertOpCodeToByteCodeEnum(*pc);
                int32_t instructionLength = getInstructionLength(bytecode, pc);

                TR::VMAccessCriticalSection vmAccess(comp);
                J9Class *currentClass = J9_CLASS_FROM_METHOD(method);
                // auto start2 = std::chrono::high_resolution_clock::now();
                executeBytecode(bytecode, pc, pag, stack, resolvedMethod, method, methodIndex, pcIndex, variableMap, hasReturnType, comp, currentClass, primitive_node, comp_type2_primitiveNode,fullNAME);
                // auto end2 = std::chrono::high_resolution_clock::now();

                // std::cout << D_PREFIX << "Time taken to execute bytecode " << getBytecodeString(bytecode) << " at bci " << pcIndex << ": "
                //           << std::chrono::duration_cast<std::chrono::microseconds>(end2 - start2).count() << " micros\n";
                pcIndex += instructionLength;
                globalIndex_++;
            }

            // propagate to successors
            for (Block *succ : bb->succs)
            {
                int succBci = succ->startBCI;
                if (inStacks.find(succ) == inStacks.end())
                {
                    inStacks[succ] = new operandStack(*stack); // copy outstack of the predecessor
                    worklist.push(succ);
                    worklist_bb_bci.insert(succBci);
                }
                else
                {
                    operandStack *succStack = inStacks[succ];

                    if (succStack->merge(*stack,fullNAME,bb->startBCI) && worklist_bb_bci.find(succBci) == worklist_bb_bci.end())
                    {
                        worklist_bb_bci.insert(succBci);
                        worklist.push(succ);
                    }
                }
            }
        }
        // end = std::chrono::high_resolution_clock::now();
        // elapsed_update = std::chrono::duration_cast<std::chrono::microseconds>(end - start);
        // std::cout << D_PREFIX << "Time for updating PAG for method worklist loop in traverse cfg:  " << elapsed_update.count() << " microsecs\n";
        // std::cout.flush();

        std::string fully_qualified_name = className + "." + name + signature;
        analysedMethodNames.insert(fully_qualified_name);
    }
};