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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Set<Stmt> reachable = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Set<Stmt> uselessAssignments = dfs(cfg.getEntry(), reachable, cfg, constants, liveVars);
        deadCode.addAll(cfg.getNodes());
        deadCode.removeAll(reachable);
        deadCode.addAll(uselessAssignments);
        // 确保entry和exit不在deadcode中
        deadCode.remove(cfg.getEntry());
        deadCode.remove(cfg.getExit());
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }

    public Set<Stmt> dfs(Stmt node, Set<Stmt> visited, CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants, DataflowResult<Stmt, SetFact<Var>> liveVars) {
        Set<Stmt> uselessAssignments = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        if (visited.contains(node)) {
            return uselessAssignments;
        }
        visited.add(node);
        if (node instanceof AssignStmt assignment && assignment.getLValue() instanceof Var var && !liveVars.getOutFact(node).contains(var) && hasNoSideEffect(assignment.getRValue())) {
            uselessAssignments.add(node);
        }
        if (node instanceof If ifStmt) {
            assert cfg.getSuccsOf(ifStmt).size() == 2;
            Value conditionValue = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getInFact(ifStmt));
            Stmt ifTrue = null;
            Stmt ifFalse = null;
            for (Stmt succ : cfg.getSuccsOf(ifStmt)) {
                if (succ.equals(ifStmt.getTarget())) {
                    ifTrue = succ;
                } else {
                    ifFalse = succ;
                }
            }
            if (!conditionValue.isConstant()) {
                uselessAssignments.addAll(dfs(ifTrue, visited, cfg, constants, liveVars));
                uselessAssignments.addAll(dfs(ifFalse, visited, cfg, constants, liveVars));
                return uselessAssignments;
            }
            if (conditionValue.getConstant() == 0) {
                uselessAssignments.addAll(dfs(ifFalse, visited, cfg, constants, liveVars));
                return uselessAssignments;
            }
            if (conditionValue.getConstant() == 1) {
                uselessAssignments.addAll(dfs(ifTrue, visited, cfg, constants, liveVars));
                return uselessAssignments;
            }
        }
        if (node instanceof SwitchStmt switchStmt) {
            Value conditionValue = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getInFact(switchStmt));
            if (!conditionValue.isConstant()) {
                for (Stmt succ : cfg.getSuccsOf(switchStmt)) {
                    uselessAssignments.addAll(dfs(succ, visited, cfg, constants, liveVars));
                }
                return uselessAssignments;
            } else {
                int conditionConst = conditionValue.getConstant();
                for (Pair<Integer, Stmt> switchPair : switchStmt.getCaseTargets()) {
                    if (conditionConst == switchPair.first()) {
                        uselessAssignments.addAll(dfs(switchPair.second(), visited, cfg, constants, liveVars));
                        return uselessAssignments;
                    }
                }
                uselessAssignments.addAll(dfs(switchStmt.getDefaultTarget(), visited, cfg, constants, liveVars));
                return uselessAssignments;
            }
        }
        for (Stmt succ : cfg.getSuccsOf(node)) {
            uselessAssignments.addAll(dfs(succ, visited, cfg, constants, liveVars));
        }
        return uselessAssignments;
    }
}
