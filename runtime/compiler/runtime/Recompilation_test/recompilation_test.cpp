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
#include "env/ClassTableCriticalSection.hpp"
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
extern std::vector<int32_t> smartAOTExceptionHandlerPCs(J9Method *method);
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
extern void smartAOTSeedStaticNodes(PointerAssignmentGraph *p);
extern bool smartAOTLoadThreadRelatedClasses();
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

    // SmartAOT: exception handler entries (same as the cold-run analysis).
    for (int32_t handlerPC : smartAOTExceptionHandlerPCs((J9Method *)method_block))
    {
        if (handlerPC >= 0 && handlerPC < methodSize)
            leaders.insert(handlerPC);
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

    // Receiver types of an abstract object. The allocated class of an object is kept in pointee_class_names (set at
    // the allocation site, and by the PAG loader from the node file); comp_type, class_name and static_type are not set
    // for loaded objects (static_type defaults to "no static type"), so using only those gave every receiver the same
    // type set and the inlining check could never fail.
    std::unordered_set<std::string> get_types(PAGNode* v, PointerAssignmentGraph *p) {
        std::unordered_set<std::string> types;
        for (PAGNode* obj : p->points_to(v)) {
            if (obj->type == OBJECT) {
                if (!obj->comp_type.empty() && obj->comp_type != "type1" && obj->comp_type != "COMP_TYPE_2") {
                    types.insert(obj->comp_type);
                } else if (!obj->pointee_class_names.empty()) {
                    types.insert(obj->pointee_class_names.begin(), obj->pointee_class_names.end());
                } else if (!obj->class_name.empty()) {
                    types.insert(obj->class_name);
                } else if (!obj->static_type.empty()) {
                    types.insert(obj->static_type);
                }
            }
        }
        return types;
    }

    std::unordered_set<std::string> get_types(const std::vector<PAGNode*> &vs, PointerAssignmentGraph *p) {
        std::unordered_set<std::string> types;
        for (PAGNode *v : vs) {
            std::unordered_set<std::string> t = get_types(v, p);
            types.insert(t.begin(), t.end());
        }
        return types;
    }

    // A call site "caller callee bci" has a receiver iff the callee is an instance method, i.e. its first formal
    // parameter node is 'this' (slot 0; parameters of static methods start at slot 1, see getSlotForArgument).
    // If the callee's formals are unknown, the call is treated as an instance call (conservative).
    bool callsiteHasReceiver(const std::string &callsite_key, PointerAssignmentGraph *p)
    {
        int caller = 0, callee = 0, bci = 0;
        if (sscanf(callsite_key.c_str(), "%d %d %d", &caller, &callee, &bci) != 3)
            return false;
        auto it = p->methodIndex_to_formalNodes.find(callee);
        if (it == p->methodIndex_to_formalNodes.end() || it->second.empty())
            return true;
        return it->second[0]->name == 0;
    }

    // OptCheck for function inlining (paper Sec. 3.5). Fails if, for some my in {mx} U deps(mx), a call site of my
    //   (1) was monomorphic in p and its receiver type set changed in p'   (Monomorphic-to-Polymorphic, safety), or
    //   (2) was polymorphic in p and became monomorphic in p'               (Polymorphic-to-Monomorphic, missed opportunity).
    // Methods in changedSet are skipped: a changed inlined method already fails the structural check, and the call
    // sites of a changed peeked method are not part of mx's compiled body.
    // It also fails if my has an instance call site whose receiver could not be resolved when loading the PAG
    // (methodsWithUnresolvedReceivers), since its receiver types are unknown.
    // On failure, *reason (if given) names the method and call site and gives the receiver types in p and p'.
    bool check_pa_inlining(const std::unordered_set<int> &depSet, const std::unordered_set<int> &changedSet, PointerAssignmentGraph *p_prime,
                           const std::unordered_map<int, std::unordered_map<std::string, std::unordered_set<std::string>>> &old_callsite_types,
                           const std::unordered_set<int> &methodsWithUnresolvedReceivers, std::string *reason = nullptr)
    {
        auto fail = [&](const std::string &why) {
            if (reason)
                *reason = why;
            return true;
        };
        // "caller callee bci" -> "<caller> bci <bci> -> <callee>"
        auto callsiteName = [&](const std::string &key) {
            int caller = 0, callee = 0, bci = 0;
            if (sscanf(key.c_str(), "%d %d %d", &caller, &callee, &bci) != 3)
                return key;
            return methodNameOf(p_prime, caller) + " bci " + std::to_string(bci) + " -> " +
                   (callee == -1 ? std::string("<unresolved target>") : methodNameOf(p_prime, callee));
        };
        for (int my : depSet)
        {
            if (changedSet.count(my))
                continue;
            if (methodsWithUnresolvedReceivers.count(my))
                return fail("an instance call site in " + methodNameOf(p_prime, my) + " has a receiver that could not be resolved when loading the PAG");
            auto myIt = old_callsite_types.find(my);
            if (myIt == old_callsite_types.end())
                continue;

            for (const auto &pair : myIt->second)
            {
                const std::string &callsite_key = pair.first;
                const std::unordered_set<std::string> &old_types = pair.second;

                // my is unchanged, so its call sites are still in p'. A missing entry would mean its receiver is
                // no longer known: do not skip the check silently.
                auto it = p_prime->CG.callsiteReceivers.find(callsite_key);
                if (it == p_prime->CG.callsiteReceivers.end() || it->second.empty())
                    return fail("call site " + callsiteName(callsite_key) + ": receiver no longer known in p' (types in p " + joinTypes(old_types) + ")");

                std::unordered_set<std::string> new_types = get_types(it->second, p_prime);

                if (old_types.size() == 1 && old_types != new_types)
                    return fail("monomorphic call site " + callsiteName(callsite_key) + " changed: receiver types " +
                                joinTypes(old_types) + " in p, " + joinTypes(new_types) + " in p'");

                if (old_types.size() > 1 && new_types.size() == 1)
                    return fail("polymorphic call site " + callsiteName(callsite_key) + " became monomorphic: receiver types " +
                                joinTypes(old_types) + " in p, " + joinTypes(new_types) + " in p'");
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

    // Incrementally replaces the PAG part of method my with the one of its new body my_prime_J9Method.
    // Returns false if the new body could not be analysed; the PAG must then be considered unusable.
    bool update_PAG(PointerAssignmentGraph *p, int my, J9Method *my_prime_J9Method, CallGraph *CG, string my_full_name)
    {
        if (all_loaded_classes.empty())
        {
            getall_loaded_classes(reloRuntime->comp());
        }

        if (!threadClassesIdentified)
        {
            threadClassesIdentified = true;
            getResolvedReflectiveCalls();
            // Fill the thread-class set that the analysis (executeBytecode) actually uses.
            // If the cold run did not write the file, its set was empty too, and the warm run keeps it empty.
            if (!smartAOTLoadThreadRelatedClasses())
                fprintf(stderr, "[SmartAOT] note: threadRelatedClasses.txt.gz not found; using an empty thread-class set (as the cold run did)\n");
            // Changed methods must use the same static-field nodes as the unchanged part of the loaded PAG.
            smartAOTSeedStaticNodes(p);
        }

        // traverse_cfg does not analyse library methods; do not remove the old body if it cannot be rebuilt.
        if (isLibraryMethod(my_full_name))
            return false;

        // start = std::chrono::high_resolution_clock::now();
        // Drop the sync sites and call sites recorded for the old body of my: they reference nodes that
        // removeNodes(my) deletes. traverse_cfg re-records them for the new body.
        std::string syncPrefix = std::to_string(my) + "_";
        for (auto it = p->CG.syncSites.begin(); it != p->CG.syncSites.end();)
        {
            if (it->first.compare(0, syncPrefix.size(), syncPrefix) == 0)
                it = p->CG.syncSites.erase(it);
            else
                ++it;
        }
        std::string callPrefix = std::to_string(my) + " ";
        for (auto it = p->CG.callsiteParams.begin(); it != p->CG.callsiteParams.end();)
        {
            if (it->first.compare(0, callPrefix.size(), callPrefix) == 0)
                it = p->CG.callsiteParams.erase(it);
            else
                ++it;
        }
        for (auto it = p->CG.callsiteReceivers.begin(); it != p->CG.callsiteReceivers.end();)
        {
            if (it->first.compare(0, callPrefix.size(), callPrefix) == 0)
                it = p->CG.callsiteReceivers.erase(it);
            else
                ++it;
        }

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

        bool analysed = traverse_cfg(my_prime_J9Method, p, my, comp, new PAGNode(), comp_type_2);

        // end = std::chrono::high_resolution_clock::now();
        // duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start).count();
        // std::cout << D_PREFIX << "Time taken to traverse PAG in update_PAG: " << duration << "  microseconds\n" << std::endl;
        // std::cout.flush();
        return analysed;
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

    bool containsNode(const std::unordered_set<PAGNode*>& objs, PAGNode* target) {
        for (auto* obj : objs) {
            if (obj->methodIndex == target->methodIndex && obj->bci == target->bci) {
                return true;
            }
        }
        return false;
    }

    bool REACH(PAGNode *target_obj, PAGNode *start_node, PointerAssignmentGraph *p)
    {
        const auto &objs = p->points_to(start_node);
        if (containsNode(objs, target_obj))
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
                    if (visited.find(next_node) == visited.end())
                    {
                        const auto &next_objs = p->points_to(next_node);
                        if (containsNode(next_objs, target_obj))
                            return true;
                        
                        visited.insert(next_node);
                        queue.push(next_node);
                    }
                }
            }
        }
        return false;
    }

    // Abstract objects are identified by their allocation site, which is stable across the in-place PAG update.
    static uint64_t objKey(PAGNode *obj)
    {
        return ((uint64_t)(uint32_t)obj->methodIndex << 32) | (uint32_t)obj->bci;
    }

    // ESCAPE(o, p) for all o at once: the set of objects o such that REACH(o, u, p) for some u in LEAKY(p).
    // Single multi-source traversal from all leaky nodes, following the same edges as REACH.
    // bottom_node is leaky too: library (JDK) methods are not analysed, and a call to one links its arguments to
    // bottom_node, so whatever is passed to the JDK is treated as escaping (e.g. STATIC_LIST.add(o)). Its arguments are
    // followed like the values stored into a leaky node, so that what is stored into their fields escapes as well.
    std::unordered_set<uint64_t> computeEscapingObjectKeys(PointerAssignmentGraph *p)
    {
        std::unordered_set<uint64_t> escaping;
        std::unordered_set<PAGNode *> visited;
        std::queue<PAGNode *> queue;

        for (PAGNode *u : p->getLeakyNodes())
        {
            if (u && visited.insert(u).second)
                queue.push(u);
        }
        if (p->bottom_node && visited.insert(p->bottom_node).second)
            queue.push(p->bottom_node);

        while (!queue.empty())
        {
            PAGNode *current = queue.front();
            queue.pop();

            for (PAGNode *obj : p->points_to(current))
                escaping.insert(objKey(obj));

            for (PAGEdge *e : current->incoming)
            {
                bool stored = e->type == EdgeType::PUTFIELD && !e->field.empty();
                bool passedToLibrary = current == p->bottom_node && e->type == EdgeType::ASSIGN;
                if ((stored || passedToLibrary) && visited.insert(e->src).second)
                    queue.push(e->src);
            }
        }
        return escaping;
    }

    // ESCAPE_var(v, p) for every synchronization variable in one pass. SyncVars are the variables a lock is taken on
    // (monitorenter operands, and 'this' of a synchronized instance method), recorded per sync site
    // "<methodIndex>_<bci>" (bci -1: synchronized method); ESCAPE_var(v, p) = exists o in points_to(v, p) : ESCAPE(o, p),
    // with ESCAPE(., p) given as `escaping`. Result: sync site -> ESCAPE_var.
    std::unordered_map<std::string, bool> computeSyncVarEscape(PointerAssignmentGraph *p, const std::unordered_set<uint64_t> &escaping)
    {
        std::unordered_map<std::string, bool> bySite;
        for (const auto &entry : p->CG.syncSites)
        {
            bool escapes = false;
            for (PAGNode *lockedVar : entry.second)
            {
                for (PAGNode *obj : p->points_to(lockedVar))
                {
                    if (escaping.count(objKey(obj)))
                    {
                        escapes = true;
                        break;
                    }
                }
                if (escapes)
                    break;
            }
            bool &site = bySite[entry.first];
            site = site || escapes;
        }
        return bySite;
    }

    // Debug output for OptCheck failures: the signature of a PAG method index (linear search, failures only)
    static std::string methodNameOf(PointerAssignmentGraph *p, int methodIndex)
    {
        if (p)
        {
            for (const auto &entry : p->_methodIndices)
            {
                if (entry.second == methodIndex)
                    return entry.first;
            }
        }
        return "<method " + std::to_string(methodIndex) + ">";
    }

    // "<methodIndex>_<bci>" -> "<signature> bci <bci>" (bci -1: synchronized method entry)
    static std::string syncSiteName(PointerAssignmentGraph *p, const std::string &site)
    {
        int method = 0, bci = 0;
        if (sscanf(site.c_str(), "%d_%d", &method, &bci) != 2)
            return site;
        return methodNameOf(p, method) + (bci == -1 ? std::string(" (synchronized method entry)") : " bci " + std::to_string(bci));
    }

    static std::string joinTypes(const std::unordered_set<std::string> &types)
    {
        std::vector<std::string> sorted(types.begin(), types.end());
        std::sort(sorted.begin(), sorted.end());
        std::string out = "{";
        for (size_t i = 0; i < sorted.size(); i++)
            out += (i ? ", " : "") + sorted[i];
        return out + "}";
    }

    // OptCheck for lock elision (paper Sec. 3.4), per synchronization variable:
    //   exists my in {mx} U deps(mx), v in SyncVars(my) : ESCAPE_var(v, p) != ESCAPE_var(v, p')
    // with deps(mx) the methods inlined into or peeked into while compiling mx, and ESCAPE_var(v, p) true if at least
    // one object v may point to in p reaches a leaky node. Covers Captured-to-Escaping (safety) and
    // Escaping-to-Captured (missed opportunity). The structural check keeps these methods unchanged, so their sites,
    // identified by (methodIndex, bci), denote the same site in p and p'; a site missing from one PAG counts as not
    // escaping.
    // On failure, *reason (if given) describes the site that failed; p is only used to name methods there.
    bool check_lock_elision(const std::unordered_set<int> &syncMethods,
                            const std::unordered_map<std::string, bool> &old_syncVarEscape,
                            const std::unordered_map<std::string, bool> &new_syncVarEscape,
                            PointerAssignmentGraph *p = nullptr, std::string *reason = nullptr)
    {
        auto fail = [&](const std::string &why) {
            if (reason)
                *reason = why;
            return true;
        };
        auto escName = [](bool escapes) { return escapes ? "escaping" : "captured"; };
        // sites of syncMethods present in either PAG
        auto inSyncMethods = [&](const std::string &site) {
            int method = 0, bci = 0;
            return sscanf(site.c_str(), "%d_%d", &method, &bci) == 2 && syncMethods.count(method) != 0;
        };
        for (const auto &site : old_syncVarEscape)
        {
            if (!inSyncMethods(site.first))
                continue;
            auto other = new_syncVarEscape.find(site.first);
            bool newEscapes = other != new_syncVarEscape.end() && other->second;
            if (newEscapes != site.second)
                return fail("SyncVar at " + syncSiteName(p, site.first) + ": " + escName(site.second) + " in p, " +
                            (other == new_syncVarEscape.end() ? "no such site (captured)" : escName(newEscapes)) + " in p'");
        }
        for (const auto &site : new_syncVarEscape)
        {
            if (!inSyncMethods(site.first))
                continue;
            auto other = old_syncVarEscape.find(site.first);
            bool oldEscapes = other != old_syncVarEscape.end() && other->second;
            if (oldEscapes != site.second)
                return fail("SyncVar at " + syncSiteName(p, site.first) + ": " +
                            (other == old_syncVarEscape.end() ? "no such site (captured)" : escName(oldEscapes)) + " in p, " +
                            escName(site.second) + " in p'");
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
        TR::ClassTableCriticalSection classTableLock(comp->fe());

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

    // Returns false if the method could not be analysed.
    bool traverse_cfg(J9Method *method, PointerAssignmentGraph *pag, int methodIndex, TR::Compilation *comp, PAGNode *primitive_node, PAGNode *comp_type2_primitiveNode)
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
        // Same filtering as the cold-run analysis (OMROptimizer traverse_cfg): no bytecode for abstract/native methods.
        // (The cold run does not filter by all_loaded_classes, so neither may the warm run: skipping here would drop
        // the changed method's effects from the PAG.)
        if ((romMethod->modifiers & (J9AccAbstract | J9AccNative)) != 0)
        {
            analysedMethodNames.insert(fullNAME);
            return true;
        }
        if (isLibraryMethod(fullNAME))
        {
            return false;
        }

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
            fprintf(stderr, "[SmartAOT] ERROR: formal parameter mismatch while re-analysing %s (%d reference params, %d formal nodes)\n",
                    fullNAME.c_str(), reference_params, (int)formal_param_nodes.size());
            return false;
        }

        for (int i = 0; i < reference_params; i++)
        {
            if ((romMethod->modifiers & J9AccStatic) != 0)
                variableMap[(formal_param_nodes[i]->name) - 1] = formal_param_nodes[i];
            else
                variableMap[formal_param_nodes[i]->name] = formal_param_nodes[i]; // non-static methods, slot 0 -> this
        }

        // SmartAOT: a synchronized instance method locks 'this' on entry; record it as sync site "<methodIndex>_-1".
        // (Static synchronized methods lock the Class object, which always escapes, so the lock is never elided.)
        if ((romMethod->modifiers & J9AccSynchronized) && !(romMethod->modifiers & J9AccStatic) && variableMap.count(0))
            pag->CG.syncSites[std::to_string(methodIndex) + "_-1"] = std::vector<PAGNode *>{variableMap[0]};

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

        // SmartAOT: once the normal control flow is done, analyse the exception handlers, each starting with the
        // caught exception (the bottom node) on the operand stack -- same as the cold-run analysis.
        bool handlersSeeded = false;
        auto seedExceptionHandlers = [&]() -> bool
        {
            handlersSeeded = true;
            for (int32_t handlerPC : smartAOTExceptionHandlerPCs(method))
            {
                auto handlerIt = blocks.find(handlerPC);
                if (handlerIt == blocks.end() || inStacks.count(handlerIt->second))
                    continue;
                operandStack *handlerStack = new operandStack();
                handlerStack->pushRef(pag->bottom_node);
                inStacks[handlerIt->second] = handlerStack;
                worklist.push(handlerIt->second);
                worklist_bb_bci.insert(handlerPC);
            }
            return !worklist.empty();
        };

        // start = std::chrono::high_resolution_clock::now();
        while (!worklist.empty() || (!handlersSeeded && seedExceptionHandlers()))
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
        return true;
    }
};