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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        JMethod method = csMethod.getMethod();
        if (callGraph.addReachableMethod(csMethod)) {
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            for (Stmt stmt : method.getIR()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod containerMethod;

        private final Context containerContext;

        private StmtProcessor(CSMethod containerMethod) {
            this.containerMethod = containerMethod;
            this.containerContext = containerMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        public Void visit(New stmt) {
            Obj newObj = heapModel.getObj(stmt);
            workList.addEntry(
                    csManager.getCSVar(containerContext, stmt.getLValue()),
                    PointsToSetFactory.make(csManager.getCSObj(contextSelector.selectHeapContext(containerMethod, newObj), newObj))
            );
            return null;
        }

        public Void visit(Copy stmt) {
            addPFGEdge(
                    csManager.getCSVar(containerContext, stmt.getRValue()),
                    csManager.getCSVar(containerContext, stmt.getLValue())
            );
            return null;
        }

        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod staticMethod = resolveCallee(null, stmt);
                CSCallSite callSite = csManager.getCSCallSite(containerContext, stmt);
                Context ct = contextSelector.selectContext(callSite, staticMethod);
                CSMethod m = csManager.getCSMethod(ct, staticMethod);
                if (callGraph.addEdge(new Edge<>(
                        CallKind.STATIC,
                        callSite,
                        m
                ))) {
                    addReachable(m);
                    passArgument(callSite, m);
                }
            }
            return null;
        }

        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(
                        csManager.getStaticField(stmt.getFieldRef().resolve()),
                        csManager.getCSVar(containerContext, stmt.getLValue())
                );
            }
            return null;
        }

        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(
                        csManager.getCSVar(containerContext, stmt.getRValue()),
                        csManager.getStaticField(stmt.getFieldRef().resolve())
                );
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

    private boolean reachable(Context stmtContext, Stmt stmt) {
        for (CSMethod csMethod : callGraph) {
            if (csMethod.getContext().equals(stmtContext)) {
                JMethod method = csMethod.getMethod();
                if (method.getIR().getStmts().contains(stmt)) {
                    return true;
                }
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
            if (n instanceof CSVar x) {
                Context containerContext = x.getContext();
                for (CSObj c1oi : delta) {
                    for (StoreField storeField : x.getVar().getStoreFields()) {
                        if (reachable(containerContext, storeField)) {
                            addPFGEdge(
                                    csManager.getCSVar(x.getContext(), storeField.getRValue()),
                                    csManager.getInstanceField(c1oi, storeField.getFieldRef().resolve())
                            );
                        }
                    }
                    for (LoadField loadField : x.getVar().getLoadFields()) {
                        if (reachable(containerContext, loadField)) {
                            addPFGEdge(
                                    csManager.getInstanceField(c1oi, loadField.getFieldRef().resolve()),
                                    csManager.getCSVar(x.getContext(), loadField.getLValue())
                            );
                        }
                    }
                    for (StoreArray storeArray : x.getVar().getStoreArrays()) {
                        if (reachable(containerContext, storeArray)) {
                            addPFGEdge(
                                    csManager.getCSVar(x.getContext(), storeArray.getRValue()),
                                    csManager.getArrayIndex(c1oi)
                            );
                        }
                    }
                    for (LoadArray loadArray : x.getVar().getLoadArrays()) {
                        if (reachable(containerContext, loadArray)) {
                            addPFGEdge(
                                    csManager.getArrayIndex(c1oi),
                                    csManager.getCSVar(x.getContext(), loadArray.getLValue())
                            );
                        }
                    }
                    processCall(x, c1oi);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet delta = PointsToSetFactory.make();
        for (CSObj obj : pointsToSet) {
            if (!pointer.getPointsToSet().contains(obj)) {
                delta.addObject(obj);
            }
        }
        if (!delta.isEmpty()) {
            for (CSObj obj : delta) {
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
     * @param cx   the receiver variable
     * @param c1oi set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar cx, CSObj c1oi) {
        Context containerContext = cx.getContext();
        for (Invoke l : cx.getVar().getInvokes()) {
            if (reachable(containerContext, l)) {
                JMethod m = resolveCallee(c1oi, l);
                CSCallSite cl = csManager.getCSCallSite(cx.getContext(), l);
                Context ct = contextSelector.selectContext(cl, c1oi, m);
                CSMethod ctm = csManager.getCSMethod(ct, m);
                workList.addEntry(csManager.getCSVar(ct, m.getIR().getThis()), PointsToSetFactory.make(c1oi));
                if (callGraph.addEdge(new Edge<>(getCallKind(l), cl, ctm))) {
                    addReachable(ctm);
                    passArgument(cl, ctm);
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

    private void passArgument(CSCallSite caller, CSMethod callee) {
        Context callerContext = caller.getContext();
        Context calleeContext = callee.getContext();
        Invoke l = caller.getCallSite();
        JMethod m = callee.getMethod();
        for (int i = 0; i < m.getParamCount(); i++) {
            addPFGEdge(
                    csManager.getCSVar(callerContext, l.getInvokeExp().getArg(i)),
                    csManager.getCSVar(calleeContext, m.getIR().getParam(i))
            );
        }
        if (l.getLValue() != null) {
            for (Var varReturn : m.getIR().getReturnVars()) {
                addPFGEdge(
                        csManager.getCSVar(calleeContext, varReturn),
                        csManager.getCSVar(callerContext, l.getLValue())
                );
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
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
