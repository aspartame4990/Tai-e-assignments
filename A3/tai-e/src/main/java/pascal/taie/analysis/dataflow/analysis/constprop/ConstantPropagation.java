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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.HashSet;
import java.util.Set;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact entry_out = new CPFact();
        for (Var param : cfg.getIR().getParams()) {
            if (canHoldInt(param)) {
                entry_out.update(param, Value.getNAC());
            }
        }
        return entry_out;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        Set<Var> allVars = new HashSet<>(fact.keySet());
        allVars.addAll(target.keySet());
        for (Var var : allVars) {
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if (v1.isUndef()) {
            return v2;
        }
        if (v2.isUndef()) {
            return v1;
        }
        if (v1.equals(v2)) {
            return Value.makeConstant(v1.getConstant());
        }
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact old_out = out.copy();
        out.clear();
        out.copyFrom(in);
        if ((stmt instanceof DefinitionStmt defStmt) && (defStmt.getLValue() instanceof Var lVar) && canHoldInt(lVar)) {
            out.update(lVar, evaluate(defStmt.getRValue(), in));
        }
        return !out.equals(old_out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        if (exp instanceof Var rVar) {
            return in.get(rVar).isConstant() ? Value.makeConstant(in.get(rVar).getConstant()) : (in.get(rVar).isNAC() ? Value.getNAC() : Value.getUndef());
        }
        if (exp instanceof BinaryExp bExp) {
            Var operand1 = bExp.getOperand1();
            Var operand2 = bExp.getOperand2();
            if (in.get(operand1).isConstant() && in.get(operand2).isConstant()) {
                int op1 = in.get(operand1).getConstant();
                int op2 = in.get(operand2).getConstant();
                if (bExp instanceof ArithmeticExp arithmeticExp) {
                    switch (arithmeticExp.getOperator()) {
                        case ADD -> {
                            return Value.makeConstant(op1 + op2);
                        }
                        case SUB -> {
                            return Value.makeConstant(op1 - op2);
                        }
                        case MUL -> {
                            return Value.makeConstant(op1 * op2);
                        }
                        case DIV -> {
                            return op2 == 0 ? Value.getUndef() : Value.makeConstant(op1 / op2);
                        }
                        case REM -> {
                            return op2 == 0 ? Value.getUndef() : Value.makeConstant(op1 % op2);
                        }
                    }
                }
                if (bExp instanceof ConditionExp conditionExp) {
                    switch (conditionExp.getOperator()) {
                        case EQ -> {
                            return Value.makeConstant((op1 == op2) ? 1 : 0);
                        }
                        case NE -> {
                            return Value.makeConstant((op1 != op2) ? 1 : 0);
                        }
                        case LT -> {
                            return Value.makeConstant((op1 < op2) ? 1 : 0);
                        }
                        case GT -> {
                            return Value.makeConstant((op1 > op2) ? 1 : 0);
                        }
                        case LE -> {
                            return Value.makeConstant((op1 <= op2) ? 1 : 0);
                        }
                        case GE -> {
                            return Value.makeConstant((op1 >= op2) ? 1 : 0);
                        }
                    }
                }
                if (bExp instanceof ShiftExp shiftExp) {
                    switch (shiftExp.getOperator()) {
                        case SHL -> {
                            return Value.makeConstant(op1 << op2);
                        }
                        case SHR -> {
                            return Value.makeConstant(op1 >> op2);
                        }
                        case USHR -> {
                            return Value.makeConstant(op1 >>> op2);
                        }
                    }
                }
                if (bExp instanceof BitwiseExp bitwiseExp) {
                    switch (bitwiseExp.getOperator()) {
                        case OR -> {
                            return Value.makeConstant(op1 | op2);
                        }
                        case AND -> {
                            return Value.makeConstant(op1 & op2);
                        }
                        case XOR -> {
                            return Value.makeConstant(op1 ^ op2);
                        }
                    }
                }
            }
            if (in.get(operand1).isNAC() && in.get(operand2).isConstant() && bExp instanceof ArithmeticExp arithmeticExp && (arithmeticExp.getOperator().equals(ArithmeticExp.Op.DIV) || arithmeticExp.getOperator().equals(ArithmeticExp.Op.REM)) && in.get(operand2).getConstant() == 0) {
                return Value.getUndef();
            }
            if (in.get(operand1).isNAC() || in.get(operand2).isNAC()) {
                return Value.getNAC();
            }
            return Value.getUndef();
        }
        return Value.getNAC();
    }
}
