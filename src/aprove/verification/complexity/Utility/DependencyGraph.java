package aprove.verification.complexity.Utility;

import static aprove.verification.oldframework.Utility.Collection_Util.*;
import static java.util.Collections.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

@SuppressWarnings("serial")
/** Has an edge f -> g iff there is a rule f(x1,...,xn) -> t where g occurs in t. */
public class DependencyGraph<TRS extends HasRules<? extends HasRuleForm> & HasDefinedSymbols> extends SimpleGraph<FunctionSymbol, Void> {

    private Map<FunctionSymbol, Node<FunctionSymbol>> nodes = new LinkedHashMap<>();

    public DependencyGraph(TRS trs) {
        this.addEdgesForFunctionApplications(trs, false);
    }

    public DependencyGraph(TRS trs, boolean considerNestedLhs) {
        this.addEdgesForFunctionApplications(trs, considerNestedLhs);
    }

    public DependencyGraph() {
        // do nothing
    }

    private void addEdgesForFunctionApplications(TRS trs, boolean considerNestedLhs) {
        for (HasRuleForm r : trs.getRules()) {
            Set<FunctionSymbol> starts = considerNestedLhs ? intersection(r.getLeft().getFunctionSymbols(), trs.getDefinedSymbols()) : singleton(r.getLeft().getRootSymbol());
            Set<FunctionSymbol> ends = r.getRight().getFunctionSymbols();
            ends.retainAll(trs.getDefinedSymbols());
            for (FunctionSymbol start: starts) {
                Node<FunctionSymbol> startNode = this.getNode(start);
                for (FunctionSymbol end : ends) {
                    Node<FunctionSymbol> endNode = this.getNode(end);
                    this.addEdge(startNode, endNode);
                }
            }
        }
    }

    protected Node<FunctionSymbol> getNode(FunctionSymbol symbol) {
        if (!this.nodes.containsKey(symbol)) {
            this.nodes.put(symbol, new Node<>(symbol));
        }
        return this.nodes.get(symbol);
    }

    public boolean isRecursive(AbstractRule r) {
        for (FunctionSymbol f: r.getRight().getFunctionSymbols()) {
            if (this.contains(this.nodes.get(f)) &&
                    this.contains(this.nodes.get(r.getRootSymbol())) &&
                    this.hasPath(this.nodes.get(f), this.nodes.get(r.getRootSymbol()))) {
                return true;
            }
        }
        return false;
    }

    public boolean hasPath(FunctionSymbol from, FunctionSymbol to) {
        Node<FunctionSymbol> start = this.nodes.get(from);
        Node<FunctionSymbol> end = this.nodes.get(to);
        if (this.contains(start) && this.contains(end)) {
            return this.hasPath(start, end);
        } else {
            return false;
        }
    }

    public void removeAllNodeObjects(Set<FunctionSymbol> toRemove) {
        for (FunctionSymbol s : toRemove) {
            this.removeNode(this.getNode(s));
        }
    }

    public void removeAllNodes(Set<Node<FunctionSymbol>> toRemove) {
        for (Node<FunctionSymbol> n: toRemove) {
            this.removeNode(n);
        }
    }

    @Override
    public DependencyGraph<TRS> clone() {
        DependencyGraph<TRS> res = new DependencyGraph<>();
        res.nodes.putAll(this.nodes);
        for (Node<FunctionSymbol> n: this.getNodes()) {
            res.addNode(n);
        }
        for (Edge<Void, FunctionSymbol> e: this.getEdges()) {
            res.addEdge(e);
        }
        return res;
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder sb = new StringBuilder();
        for (Pair<Node<FunctionSymbol>, Node<FunctionSymbol>> p: Collection_Util.getPairs(this.getNodes())) {
            if (this.hasPath(p.x, p.y) && this.hasPath(p.y, p.x)) {
                sb.append(p.x.getObject().export(eu));
                sb.append(eu.appSpace());
                sb.append(eu.eqSign());
                sb.append(eu.appSpace());
                sb.append(p.y.getObject().export(eu));
                sb.append(eu.linebreak());
            } else if (this.contains(p.x, p.y)) {
                sb.append(p.y.getObject().export(eu));
                sb.append(eu.appSpace());
                sb.append(eu.ltSign());
                sb.append(eu.appSpace());
                sb.append(p.x.getObject().export(eu));
                sb.append(eu.linebreak());
            } else if (this.contains(p.y, p.x)) {
                sb.append(p.x.getObject().export(eu));
                sb.append(eu.appSpace());
                sb.append(eu.ltSign());
                sb.append(eu.appSpace());
                sb.append(p.y.getObject().export(eu));
                sb.append(eu.linebreak());
            }
        }
        return sb.toString();
    }

    public void remove(FunctionSymbol f) {
        this.removeNode(this.nodes.get(f));
    }
}
