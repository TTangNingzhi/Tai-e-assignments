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
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

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
        CPFact fact = new CPFact();
        cfg.getIR().getParams().forEach(param -> {
            if (canHoldInt(param)) {
                fact.update(param, Value.getNAC());
            }
        });
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var key : fact.keySet()) {
            Value v1 = fact.get(key);
            Value v2 = target.get(key);
            target.update(key, meetValue(v1, v2));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef() && v2.isConstant()) {
            return v2;
        } else if (v2.isUndef() && v1.isConstant()) {
            return v1;
        } else if (v1.isConstant() && v2.isConstant()) {
            if (v1.equals(v2)) {
                return v1;
            } else {
                return Value.getNAC();
            }
        } else {
            return Value.getUndef();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact oldOut = out.copy();
        out.clear();
        for (Var key : in.keySet()) {
            out.update(key, in.get(key));
        }
        if (stmt instanceof DefinitionStmt<?, ?> def) {
            if (def.getLValue() instanceof Var var && canHoldInt(var)) {
                Value value = evaluate(def.getRValue(), in);
                out.update(var, value);
            }
        }
        return !out.equals(oldOut);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE, SHORT, INT, CHAR, BOOLEAN -> {
                    return true;
                }
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
        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        } else if (exp instanceof Var var && canHoldInt(var)) {
            return in.get(var);
        } else if (exp instanceof BinaryExp binaryExp) {
            Value v1 = evaluate(binaryExp.getOperand1(), in);
            Value v2 = evaluate(binaryExp.getOperand2(), in);
            // for x / 0 and x % 0, return undef even if x is NAC
            if (binaryExp instanceof ArithmeticExp arithmeticExp
                    && (arithmeticExp.getOperator() == ArithmeticExp.Op.DIV || arithmeticExp.getOperator() == ArithmeticExp.Op.REM)
                    && v2.isConstant() && v2.getConstant() == 0) {
                return Value.getUndef();
            }
            if (v1.isNAC() || v2.isNAC()) {
                return Value.getNAC();
            } else if (v1.isConstant() && v2.isConstant()) {
                int i1 = v1.getConstant();
                int i2 = v2.getConstant();
                if (binaryExp instanceof ArithmeticExp arithmeticExp) {
                    switch (arithmeticExp.getOperator()) {
                        case ADD -> {
                            return Value.makeConstant(i1 + i2);
                        }
                        case SUB -> {
                            return Value.makeConstant(i1 - i2);
                        }
                        case MUL -> {
                            return Value.makeConstant(i1 * i2);
                        }
                        case DIV -> {
                            return Value.makeConstant(i1 / i2);
                        }
                        case REM -> {
                            return Value.makeConstant(i1 % i2);
                        }
                    }
                } else if (binaryExp instanceof ConditionExp conditionExp) {
                    switch (conditionExp.getOperator()) {
                        case EQ -> {
                            return Value.makeConstant(i1 == i2 ? 1 : 0);
                        }
                        case NE -> {
                            return Value.makeConstant(i1 != i2 ? 1 : 0);
                        }
                        case LT -> {
                            return Value.makeConstant(i1 < i2 ? 1 : 0);
                        }
                        case LE -> {
                            return Value.makeConstant(i1 <= i2 ? 1 : 0);
                        }
                        case GT -> {
                            return Value.makeConstant(i1 > i2 ? 1 : 0);
                        }
                        case GE -> {
                            return Value.makeConstant(i1 >= i2 ? 1 : 0);
                        }
                    }
                } else if (binaryExp instanceof BitwiseExp bitwiseExp) {
                    switch (bitwiseExp.getOperator()) {
                        case OR -> {
                            return Value.makeConstant(i1 | i2);
                        }
                        case AND -> {
                            return Value.makeConstant(i1 & i2);
                        }
                        case XOR -> {
                            return Value.makeConstant(i1 ^ i2);
                        }
                    }
                } else if (binaryExp instanceof ShiftExp shiftExp) {
                    switch (shiftExp.getOperator()) {
                        case SHL -> {
                            return Value.makeConstant(i1 << i2);
                        }
                        case SHR -> {
                            return Value.makeConstant(i1 >> i2);
                        }
                        case USHR -> {
                            return Value.makeConstant(i1 >>> i2);
                        }
                    }
                } else {
                    return Value.getUndef();
                }
            } else {
                return Value.getUndef();
            }
        }
        return Value.getNAC();
    }
}
