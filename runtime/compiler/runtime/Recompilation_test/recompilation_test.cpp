#pragma once
#include "omr/compiler/optimizer/PAG/PointerAssignmentGraph.cpp"
#include "omr/compiler/optimizer/PAG/CallGraph.cpp"
#include "omr/compiler/optimizer/PAG/regularPT.cpp"
#include <unordered_set>
#include <unordered_map>
#include <queue>
#include <set>
#include <vector>
#include "methodSet.cpp"
#include "RelocationRuntime.hpp"

extern MethodSet computeMSetForMethod(TR::Compilation *comp, TR::ResolvedMethodSymbol *methodSymbol);
extern TR_ResolvedMethod *getCachedResolvedMethodFromPtr(TR::Compilation *comp, TR_OpaqueMethodBlock *methodPtr);
class recompilation_test {
public:
   
    TR_RelocationRuntime *reloRuntime;


    // boolean REACH(Node target_obj, Node start_node, PAG p):
     bool REACH(PAGNode* target_obj, PAGNode* start_node, PointerAssignmentGraph* p) {
        // Case 1:
        std::unordered_set<PAGNode*> objs = p->points_to(start_node);
        if (objs.find(target_obj) != objs.end())
            return true;

        std::set<std::pair<PAGNode*, std::vector<std::string>>> visited;

        // Queue for BFS traversal (object, field_path)
        std::queue<std::pair<PAGNode*, std::vector<std::string>>> queue;

        // Enqueue all objects directly pointed to by start_node
        for (PAGNode* obj : objs) {
            queue.push({obj, {}});
            visited.insert({obj, {}});
        }

        while (!queue.empty()) {
            auto front = queue.front();
            auto current_obj = front.first;
            auto field_path = front.second;
            queue.pop();

            // Check if current object matches target_obj
            if (current_obj == target_obj)
                return true;

            // Explore fields of the current object
            for (std::string field : p->get_fields(current_obj)) {
                
                auto next_objs = p->get_field_target(current_obj, field);
                auto new_field_path = field_path;
                new_field_path.push_back(field);

                for (PAGNode* next_obj : next_objs) {
                    auto path_key = std::make_pair(next_obj, new_field_path);

                    if (visited.find(path_key) == visited.end()) {
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

    // boolean should_recompile(Method mx,Method my_prime,PAG p_prime,PAG p)
     bool should_recompile(int mx, int my_prime,PointerAssignmentGraph* p_prime,unordered_set<PAGEdge *> old_allocated_edges,unordered_set<PAGNode *> old_escaping_objects) {
        // Get allocated objects in mx
        // auto old_allocated_edges = p->getAllocEdges(mx); // E: o1 --NEW--> temp, for stmt `temp: new A()` in il-trees

        // Get escaping objects in mx in p
        // auto old_escaping_objects = p->getEscapingObjects(mx);   

        // Get leaky nodes in the updated PAG p'
        auto leaky_nodes = p_prime->getLeakyNodes();

        for (PAGEdge* alloc_edge : old_allocated_edges) {
            PAGNode* o = alloc_edge->src;

            bool isEscaping = std::find(old_escaping_objects.begin(), old_escaping_objects.end(), o) != old_escaping_objects.end();

            if (isEscaping) {
                // Ensure no reachable path from any leaky node
                bool isReachable = false;

                // [ \forall u \in leaky_nodes , ~REACH(o,u) ] => recompile mx
                for (PAGNode* u : leaky_nodes) {
                    isReachable |= REACH(o, u, p_prime);
                }

                if (isReachable == false)
                    return true;  // Recompile mx
            } 
            else {
                // \exists u \in leaky_nodes , REACH(o,u) => recompile mx
                for (PAGNode* u : leaky_nodes) {
                    if (REACH(o, u, p_prime)) {
                        return true;  // Recompile mx
                    }
                }
            }
        }

        return false;  // No recompilation needed
    }

     PointerAssignmentGraph* update_PAG(PointerAssignmentGraph* p, int my,TR_OpaqueMethodBlock* my_prime_methodBlock , CallGraph* CG) {

        // remove interprocedural edges [All the edges to formal params are `assign` edges]
        for (PAGNode* f_param : p->getFormalParameterNodes(my)) {
            p->removeAllEdgesFrom(f_param);
        }

        for (int caller : CG->getCallers(my)) {
            for (auto cs : CG->getCallSites(caller, my)) {
                for (PAGNode* a_param : p->getActualParameterNodes(my,cs)) {
                    // remove edge from the actual paramter labelled by the callsite cs
                    p->removeEdgeFrom(a_param, cs);
                }

                PAGNode* ret_my = p->getReturnNode(my);
                if (ret_my != NULL) {
                    p->removeAllEdgesFrom(ret_my);
                    // remove edge from the x labelled by the callsite cs
                    // Assume x is externally known
                    PAGNode* x = p->nodeIndexToNode[p->callsite_to_storeNodeIndex[cs]];
                    p->removeEdgeFrom(x,cs);
                }
            }
        }

        // remove match edges
        for (PAGEdge* e1 : p->getStoreEdges(my)) {
            for (PAGEdge* e2 : p->getLoadEdges(my)) {
                if (e1->field == e2->field) { 
                    p->removeEdgeFrom(e1->src, MATCH); 
                    p->removeEdgeFrom(e2->dest, MATCH_BAR);
                }
            }
        }

        // remove intraprocedural edges
        // Assume remove call will remove both edges labelled by k and k_bar
        for (PAGEdge* e : p->getIntraproceduralAssignEdges(my))
             p->removeEdge(e);
        for (PAGEdge* e : p->getAllocEdges(my)) 
            p->removeEdge(e);

        for (PAGEdge* e : p->getStoreEdges(my)) {
            // f is  field or field of a class extending Thread or implementing Runnable,
            // then remove x from the leaky nodes set
            if (isStaticField(e->field,p) || isThreadClassField(e->field,p)) {
                p->LeakyNodes.erase(e->src);
            }
            p->removeEdge(e);
        }

        for (PAGEdge* e : p->getLoadEdges(my)) 
            p->removeEdge(e);

        p->removeNodes(my);

        // add intraprocedural edges
        // Assume addEdge(flowsToSrc,flowsToTarget,label) call with label k
        // will also add the reverse edge with label k_bar
        // TODO: add intraprocedural edges
        // use computeMSetForMethod(TR::Compilation *comp, TR::ResolvedMethodSymbol *methodSymbol)
        // computeMsetForMethod call will create all the nodes for actual/formal and return nodes and also add the edges(both intra/inter)
            TR::Compilation *comp = reloRuntime->comp();
            // TR::ResolvedMethodSymbol *methodSymbol = 
            // Get TR_OpaqueMethodBlock* from method index
            // TR_OpaqueMethodBlock* methodBlock = nullptr;
            // for (auto& entry : _methodIndicesPtr) {
            //     if (entry.second == my) {
            //         methodBlock = entry.first;
            //         break;
            //     }
            // }
            // if (!methodBlock) {
            //     return;
            // }

            TR_ResolvedMethod* resolvedMethod = getCachedResolvedMethodFromPtr(comp, my_prime_methodBlock);
            TR::ResolvedMethodSymbol* methodSymbol = resolvedMethod->findOrCreateJittedMethodSymbol(comp);

            // Get frontend and generate IL
            TR_J9VMBase* fe = (TR_J9VMBase*)comp->fe();
           bool ilGenFailed = NULL == resolvedMethod->genMethodILForPeekingEvenUnderMethodRedefinition(methodSymbol, comp, false);
           TR_ASSERT_FATAL(!ilGenFailed, "IL Gen failed for my_prime");


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
        for (PAGEdge* e1 : p->getStoreEdges(my)) {
            for (PAGEdge* e2 : p->getLoadEdges(my)) {
                if (e1->field == e2->field) {
                    p->addEdge(e1->src, e2->dest, MATCH);
                }
            }
        }

        return p;
    }

    // set<string> get_fields(AbstractNode obj)
     std::unordered_set<std::string> get_fields(PointerAssignmentGraph* p, PAGNode* obj) {
        std::unordered_set<string> fields;
        // if there is a putfield to this node then its having a field labelled in the edge label
        for (PAGNode* node : p->flowsTo(obj)) {
            for (PAGEdge* e : p->getStoreEdges()) {
                if (e->dest == node) {
                    fields.insert(e->field);
                }
            }
        }
        return fields;
    }

    // set<AbstractNodes> get_field_target(AbstractNode current_obj, string field)
     std::unordered_set<PAGNode*> get_field_target(PointerAssignmentGraph* p, PAGNode* obj, std::string field) {
        std::unordered_set<PAGNode*> targets;
        for (PAGEdge* e : p->getStoreEdges()) {
            if (e->dest == obj && e->field == field) {
                targets.insert(e->src);
            }
        }
        return targets;
    }

     bool isStaticField(std::string field,PointerAssignmentGraph* p) {
       
        return p->staticFields.find(field) != p->staticFields.end();
    }

     bool isThreadClassField(std::string field,PointerAssignmentGraph* p) {
       
        return p->threadAccessibleFields.find(field) != p->threadAccessibleFields.end();
    }
};