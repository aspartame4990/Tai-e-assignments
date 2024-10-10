/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (callGraph.addReachableMethod(method)) {
            for (Stmt stmt : method.getIR()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        public Void visit(New stmt) {
            workList.addEntry(pointerFlowGraph.getVarPtr(stmt.getLValue()), new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }

        public Void visit(Copy stmt) {
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }

        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod m = resolveCallee(null, stmt);
                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, m))) {
                    addReachable(m);
                    passArgument(stmt, m);
                }
            }
            return null;
        }

        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            }
            return null;
        }

        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()));
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    private boolean reachable(Stmt stmt) {
        for (JMethod method: callGraph) {
            if(method.getIR().getStmts().contains(stmt)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry n_pts = workList.pollEntry();
            Pointer n = n_pts.pointer();
            PointsToSet pts = n_pts.pointsToSet();
            PointsToSet delta = propagate(n, pts);
            if (n instanceof VarPtr x) {
                for (Obj oi : delta) {
                    for (StoreField storeField : x.getVar().getStoreFields()) {
                        if (reachable(storeField)) {
                            Var y = storeField.getRValue();
                            addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getInstanceField(oi, storeField.getFieldRef().resolve()));
                        }
                    }
                    for (LoadField loadField : x.getVar().getLoadFields()) {
                        if (reachable(loadField)) {
                            Var y = loadField.getLValue();
                            addPFGEdge(pointerFlowGraph.getInstanceField(oi, loadField.getFieldRef().resolve()), pointerFlowGraph.getVarPtr(y));
                        }
                    }
                    for (StoreArray storeArray : x.getVar().getStoreArrays()) {
                        if (reachable(storeArray)) {
                            Var y = storeArray.getRValue();
                            addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getArrayIndex(oi));
                        }
                    }
                    for (LoadArray loadArray : x.getVar().getLoadArrays()) {
                        if (reachable(loadArray)) {
                            Var y = loadArray.getLValue();
                            addPFGEdge(pointerFlowGraph.getArrayIndex(oi), pointerFlowGraph.getVarPtr(y));
                        }
                    }
                    processCall(x.getVar(), oi);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet delta = new PointsToSet();
        for (Obj obj : pointsToSet) {
            if (!pointer.getPointsToSet().contains(obj)) {
                delta.addObject(obj);
            }
        }
        if (!delta.isEmpty()) {
            for (Obj obj : delta) {
                pointer.getPointsToSet().addObject(obj);
            }
            for (Pointer successor : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(successor, delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param x  the variable that holds receiver objects
     * @param oi a new discovered object pointed by the variable.
     */
    private void processCall(Var x, Obj oi) {
        for (Invoke l : x.getInvokes()) {
            if (reachable(l)) {
                JMethod m = resolveCallee(oi, l);
                workList.addEntry(pointerFlowGraph.getVarPtr(m.getIR().getThis()), new PointsToSet(oi));
                if (callGraph.addEdge(new Edge<>(getCallKind(l), l, m))) {
                    addReachable(m);
                    passArgument(l, m);
                }
            }
        }
    }

    private CallKind getCallKind(Invoke invoke) {
        if (invoke.isStatic()) {
            return CallKind.STATIC;
        }
        if (invoke.isInterface()) {
            return CallKind.INTERFACE;
        }
        if (invoke.isSpecial()) {
            return CallKind.SPECIAL;
        }
        if (invoke.isVirtual()) {
            return CallKind.VIRTUAL;
        }
        assert false;
        return null;
    }

    private void passArgument(Invoke l, JMethod m) {
        for (int i = 0; i < m.getParamCount(); i++) {
            addPFGEdge(pointerFlowGraph.getVarPtr(l.getInvokeExp().getArg(i)), pointerFlowGraph.getVarPtr(m.getIR().getParam(i)));
        }
        if (l.getLValue() != null) {
            for (Var varReturn : m.getIR().getReturnVars()) {
                addPFGEdge(pointerFlowGraph.getVarPtr(varReturn), pointerFlowGraph.getVarPtr(l.getLValue()));
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
