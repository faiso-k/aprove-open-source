package aprove.verification.complexity.LowerBounds.AnalysisOrder;

import java.util.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;


@SuppressWarnings("serial")
/** Like a DependencyGraph, but without self-loops, non-recursive symbols and 'auxiliary-functions' (which are determined heuristically) */
public class SimplifiedDependencyGraph extends DependencyGraph<LowerBoundsTrs> {

    public SimplifiedDependencyGraph(LowerBoundsTrs trs) {
        super(trs);
        this.removeAcyclicNodes();
        this.removeAuxiliaryFunctions();
        this.removeSelfLoops();
    }

    private void removeAcyclicNodes() {
        Set<Node<FunctionSymbol>> toRemove = new LinkedHashSet<>();
        for (Node<FunctionSymbol> node : this.getNodes()) {
            if (!this.hasPath(node, node, false, null)) {
                toRemove.add(node);
            }
        }
        this.removeAllNodes(toRemove);
    }

    private void removeAuxiliaryFunctions() {
        Set<Node<FunctionSymbol>> toRemove = new LinkedHashSet<>();
        for (Node<FunctionSymbol> node : this.getNodes()) {
            Set<Node<FunctionSymbol>> preds = this.getIn(node);
            preds.removeAll(toRemove);
            if (preds.size() == 1 && !preds.contains(node)) {
                FunctionSymbol pred = preds.iterator().next().getObject();
                if (this.firstIsSimpler(pred, node.getObject())) {
                    toRemove.add(node);
                    Set<Node<FunctionSymbol>> successors = this.getOut(node);
                    for (Node<FunctionSymbol> succ: successors) {
                        this.addEdge(this.getNode(pred), succ);
                    }
                }
            }
        }
        this.removeAllNodes(toRemove);
    }

    private boolean firstIsSimpler(FunctionSymbol first, FunctionSymbol second) {
        return first.getArity() < second.getArity();
    }

    private void removeSelfLoops() {
        Set<Edge<Void, FunctionSymbol>> toRemove = new LinkedHashSet<>();
        for (Edge<Void, FunctionSymbol> e: this.getEdges()) {
            if (e.getStartNode().equals(e.getEndNode())) {
                toRemove.add(e);
            }
        }
        this.removeAllEdges(toRemove);
    }

    public void removeAllEdges(Set<Edge<Void, FunctionSymbol>> toRemove) {
        for (Edge<Void, FunctionSymbol> e: toRemove) {
            this.removeEdge(e);
        }
    }

}
