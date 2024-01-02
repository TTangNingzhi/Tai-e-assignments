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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.ir.exp.Var;

class IterativeSolver<Node, Fact> extends Solver<Node, Fact> {

    public IterativeSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        boolean changed = true;
        while (changed) {
            changed = false;
            for (Node node : cfg.getNodes()) {
                if (!cfg.isExit(node)) {
                    // OUT[B] = MEET(IN[S1], IN[S2], ..., IN[Sn])
                    Fact outFact = analysis.newInitialFact();
                    for (Node succ : cfg.getSuccsOf(node)) {
                        analysis.meetInto(result.getInFact(succ), outFact);
                    }
                    result.setOutFact(node, outFact);
                    // IN[B] = TRANSFER(OUT[B])
                    Fact inFact = result.getInFact(node);
                    boolean curChanged = analysis.transferNode(node, inFact, outFact);
                    if (curChanged) {
                        changed = true;
                    }
                    result.setInFact(node, inFact);
                }
            }
        }
    }
}
