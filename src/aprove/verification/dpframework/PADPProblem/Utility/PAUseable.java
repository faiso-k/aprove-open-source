package aprove.verification.dpframework.PADPProblem.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.PADPProblem.*;
import aprove.verification.dpframework.PATRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

public class PAUseable {

    private PADPProblem padp;

    private SimpleGraph<FunctionSymbol, Object> depGraph;
    private Map<FunctionSymbol, Node<FunctionSymbol>> nodeMap;

    public PAUseable(PADPProblem padp) {
        this.padp = padp;
        this.depGraph = null;
        this.nodeMap = null;
    }

    /**
     * Computes the usable PATRS for a given set of DPs.
     */
    public PATRSProblem getUseable(Collection<PARule> dps) {
        if (this.depGraph == null) {
            this.calcDepGraph();
        }
        return this.calcUseable(dps);
    }

    private void calcDepGraph() {
        Set<Node<FunctionSymbol>> nodes = new LinkedHashSet<Node<FunctionSymbol>>();
        this.nodeMap = new LinkedHashMap<FunctionSymbol, Node<FunctionSymbol>>();
        for (FunctionSymbol f : this.padp.getSignatureNoTuple()) {
            Node<FunctionSymbol> node = new Node<FunctionSymbol>(f);
            this.nodeMap.put(f, node);
            nodes.add(node);
        }
        this.depGraph = new SimpleGraph<FunctionSymbol, Object>(nodes);

        for (PARule rule : this.padp.getR()) {
            this.addDelta(rule.getLeft(), rule.getRight());
        }
        for (Rule rule : this.padp.getS()) {
            this.addDelta(rule.getLeft(), rule.getRight());
        }
        for (Equation eqn : this.padp.getE()) {
            this.addDelta(eqn.getLeft(), eqn.getRight());
            this.addDelta(eqn.getRight(), eqn.getLeft());
        }
    }

    private void addDelta(TRSTerm l, TRSTerm r) {
        if (!l.isVariable()) {
            this.addDelta(((TRSFunctionApplication) l).getRootSymbol(), r);
        }
    }

    private void addDelta(FunctionSymbol f, TRSTerm r) {
        Set<FunctionSymbol> funs = r.getFunctionSymbols();
        for (FunctionSymbol ff : funs) {
            this.addEdge(f, ff);
        }
    }

    private void addEdge(FunctionSymbol f, FunctionSymbol g) {
        if (!f.equals(g)) {
            Node<FunctionSymbol> from = this.nodeMap.get(f);
            Node<FunctionSymbol> to = this.nodeMap.get(g);
            this.depGraph.addEdge(from, to);
        }
    }

    private PATRSProblem calcUseable(Collection<PARule> dps) {
        Set<FunctionSymbol> delta = new LinkedHashSet<FunctionSymbol>();
        for (PARule dp : dps) {
            Set<FunctionSymbol> dpfs = dp.getRight().getFunctionSymbols();
            dpfs.remove(((TRSFunctionApplication) dp.getRight()).getRootSymbol());
            delta.addAll(dpfs);
        }

        //ImmutableMap<String, ImmutableList<String>> sortMap = this.padp.getSortMap();
        //for (FunctionSymbol f : this.padp.getSignatureNoTuple()) {
        //    ImmutableList<String> arr = sortMap.get(f.getName());
        //    if (arr.get(f.getArity()).equals("int")) {
        //        delta.add(f);
        //    }
        //}

        Set<Node<FunctionSymbol>> deltanodes = new LinkedHashSet<Node<FunctionSymbol>>();
        for (FunctionSymbol f : delta) {
            deltanodes.add(this.nodeMap.get(f));
        }

        Set<Node<FunctionSymbol>> deltastarnodes = this.depGraph.determineReachableNodes(deltanodes);
        Set<FunctionSymbol> deltastar = new LinkedHashSet<FunctionSymbol>();
        for (Node<FunctionSymbol> node : deltastarnodes) {
            deltastar.add(node.getObject());
        }

        deltastar.add(FunctionSymbol.create("0", 0));
        deltastar.add(FunctionSymbol.create("1", 0));
        deltastar.add(FunctionSymbol.create("-", 1));
        deltastar.add(FunctionSymbol.create("+", 2));

        ImmutableSet<PARule> newR = ImmutableCreator.create(this.getR(this.padp.getR(), deltastar));
        ImmutableSet<Rule> newS = ImmutableCreator.create(this.getS(this.padp.getS(), deltastar));
        ImmutableSet<Equation> newE = ImmutableCreator.create(this.getE(this.padp.getE(), deltastar));
        return PATRSProblem.create(newR, newS, newE, this.padp.getSortMap());
    }

    private Set<PARule> getR(ImmutableSet<PARule> r, Set<FunctionSymbol> funs) {
        Set<PARule> res = new LinkedHashSet<PARule>();
        for (PARule rule : r) {
            if (funs.contains(rule.getLeft().getRootSymbol())) {
                res.add(rule);
            }
        }
        return res;
    }

    private Set<Rule> getS(ImmutableSet<Rule> s, Set<FunctionSymbol> funs) {
        Set<Rule> res = new LinkedHashSet<Rule>();
        for (Rule rule : s) {
            if (funs.contains(rule.getLeft().getRootSymbol())) {
                res.add(rule);
            }
        }
        return res;
    }

    private Set<Equation> getE(ImmutableSet<Equation> e, Set<FunctionSymbol> funs) {
        Set<Equation> res = new LinkedHashSet<Equation>();
        for (Equation eqn : e) {
            if (funs.contains(((TRSFunctionApplication) eqn.getLeft()).getRootSymbol())) {
                res.add(eqn);
            } else if (funs.contains(((TRSFunctionApplication) eqn.getRight()).getRootSymbol())) {
                res.add(eqn);
            }
        }
        return res;
    }

}
