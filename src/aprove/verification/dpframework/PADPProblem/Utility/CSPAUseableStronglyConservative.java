package aprove.verification.dpframework.PADPProblem.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.PADPProblem.*;
import aprove.verification.dpframework.PATRSProblem.*;
import aprove.verification.dpframework.PATRSProblem.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

public class CSPAUseableStronglyConservative {

    private CSPADPProblem cspadp;

    private SimpleGraph<FunctionSymbol, Object> depGraph;
    private SimpleGraph<FunctionSymbol, Object> overlineDepGraph;
    private Map<FunctionSymbol, Node<FunctionSymbol>> nodeMap;
    private Map<FunctionSymbol, Node<FunctionSymbol>> overlineNodeMap;
    private Set<FunctionSymbol> funsSE;

    public CSPAUseableStronglyConservative(CSPADPProblem cspadp) {
        this.cspadp = cspadp;
        this.funsSE = cspadp.getSignatureSE();
        this.depGraph = null;
        this.overlineDepGraph = null;
        this.nodeMap = null;
        this.overlineNodeMap = null;
    }

    /**
     * Computes the usable CSPATRS for a given set of DPs.
     */
    public CSPATRSProblem getUseable(Collection<PARule> dps) {
        if (this.depGraph == null || this.overlineDepGraph == null) {
            this.calcDepGraph();
        }
        return this.calcUseable(dps);
    }

    private void calcDepGraph() {
        Set<Node<FunctionSymbol>> nodes = new LinkedHashSet<Node<FunctionSymbol>>();
        Set<Node<FunctionSymbol>> overlineNodes = new LinkedHashSet<Node<FunctionSymbol>>();
        this.nodeMap = new LinkedHashMap<FunctionSymbol, Node<FunctionSymbol>>();
        this.overlineNodeMap = new LinkedHashMap<FunctionSymbol, Node<FunctionSymbol>>();
        for (FunctionSymbol f : this.cspadp.getSignatureNoTuple()) {
            Node<FunctionSymbol> node = new Node<FunctionSymbol>(f);
            Node<FunctionSymbol> overlineNode = new Node<FunctionSymbol>(f);
            this.nodeMap.put(f, node);
            this.overlineNodeMap.put(f, overlineNode);
            nodes.add(node);
            overlineNodes.add(overlineNode);
        }
        this.depGraph = new SimpleGraph<FunctionSymbol, Object>(nodes);
        this.overlineDepGraph = new SimpleGraph<FunctionSymbol, Object>(overlineNodes);

        for (PARule rule : this.cspadp.getR()) {
            this.addDelta(rule.getLeft(), rule.getRight(), this.cspadp.getMu());
        }
        for (Rule rule : this.cspadp.getS()) {
            this.addDelta(rule.getLeft(), rule.getRight(), null);
        }
        for (Equation eqn : this.cspadp.getE()) {
            this.addDelta(eqn.getLeft(), eqn.getRight(), null);
            this.addDelta(eqn.getRight(), eqn.getLeft(), null);
        }
    }

    private void addDelta(TRSTerm l, TRSTerm r, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        if (!l.isVariable()) {
            this.addDelta(((TRSFunctionApplication) l).getRootSymbol(), r, mu);
        }
    }

    private void addDelta(FunctionSymbol f, TRSTerm r, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        Set<FunctionSymbol> funs = null;
        Set<FunctionSymbol> overlineFuns = r.getFunctionSymbols();
        if (mu == null) {
            funs = r.getFunctionSymbols();
        } else {
            funs = this.getActive(r, mu);
            funs.addAll(this.getFunsSE(r, this.funsSE));
        }
        for (FunctionSymbol ff : funs) {
            this.addEdge(f, ff);
        }
        for (FunctionSymbol ff : overlineFuns) {
            this.addOverlineEdge(f, ff);
        }
    }

    private Set<FunctionSymbol> getActive(TRSTerm r, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        Set<FunctionSymbol> res = new LinkedHashSet<FunctionSymbol>();
        for (TRSTerm t : CSTermHelper.getActiveSubterms(r, mu)) {
            if (!t.isVariable()) {
                res.add(((TRSFunctionApplication) t).getRootSymbol());
            }
        }
        return res;
    }

    private void addEdge(FunctionSymbol f, FunctionSymbol g) {
        if (!f.equals(g)) {
            Node<FunctionSymbol> from = this.nodeMap.get(f);
            Node<FunctionSymbol> to = this.nodeMap.get(g);
            this.depGraph.addEdge(from, to);
        }
    }

    private void addOverlineEdge(FunctionSymbol f, FunctionSymbol g) {
        if (!f.equals(g)) {
            Node<FunctionSymbol> from = this.overlineNodeMap.get(f);
            Node<FunctionSymbol> to = this.overlineNodeMap.get(g);
            this.overlineDepGraph.addEdge(from, to);
        }
    }

    private Set<FunctionSymbol> getFunsSE(TRSTerm t, Set<FunctionSymbol> funs) {
        Set<FunctionSymbol> res = t.getFunctionSymbols();
        res.retainAll(funs);
        return res;
    }

    private CSPATRSProblem calcUseable(Collection<PARule> dps) {
        Set<FunctionSymbol> delta = new LinkedHashSet<FunctionSymbol>();
        Set<FunctionSymbol> overlinedelta = new LinkedHashSet<FunctionSymbol>();
        for (PARule dp : dps) {
            Set<FunctionSymbol> dpfs = this.getActive(dp.getRight(), this.cspadp.getMu());
            Set<FunctionSymbol> overlinedpfs = dp.getRight().getFunctionSymbols();
            FunctionSymbol tupleSymbol = ((TRSFunctionApplication) dp.getRight()).getRootSymbol();
            dpfs.remove(tupleSymbol);
            overlinedpfs.remove(tupleSymbol);
            dpfs.addAll(this.getFunsSE(dp.getRight(), this.funsSE));
            delta.addAll(dpfs);
            overlinedelta.addAll(overlinedpfs);
        }

        Set<Node<FunctionSymbol>> deltanodes = new LinkedHashSet<Node<FunctionSymbol>>();
        for (FunctionSymbol f : delta) {
            deltanodes.add(this.nodeMap.get(f));
        }
        Set<Node<FunctionSymbol>> overlinedeltanodes = new LinkedHashSet<Node<FunctionSymbol>>();
        for (FunctionSymbol f : overlinedelta) {
            overlinedeltanodes.add(this.overlineNodeMap.get(f));
        }

        Set<Node<FunctionSymbol>> deltastarnodes = this.depGraph.determineReachableNodes(deltanodes);
        Set<FunctionSymbol> deltastar = new LinkedHashSet<FunctionSymbol>();
        for (Node<FunctionSymbol> node : deltastarnodes) {
            deltastar.add(node.getObject());
        }

        Set<Node<FunctionSymbol>> overlinedeltastarnodes = this.overlineDepGraph.determineReachableNodes(overlinedeltanodes);
        Set<FunctionSymbol> overlinedeltastar = new LinkedHashSet<FunctionSymbol>();
        for (Node<FunctionSymbol> node : overlinedeltastarnodes) {
            overlinedeltastar.add(node.getObject());
        }

        overlinedeltastar.add(FunctionSymbol.create("0", 0));
        overlinedeltastar.add(FunctionSymbol.create("1", 0));
        overlinedeltastar.add(FunctionSymbol.create("-", 1));
        overlinedeltastar.add(FunctionSymbol.create("+", 2));

        ImmutableSet<PARule> newR = ImmutableCreator.create(this.getR(this.cspadp.getR(), deltastar));
        ImmutableSet<Rule> newS = ImmutableCreator.create(this.getS(this.cspadp.getS(), overlinedeltastar));
        ImmutableSet<Equation> newE = ImmutableCreator.create(this.getE(this.cspadp.getE(), overlinedeltastar));
        return CSPATRSProblem.create(newR, newS, newE, this.cspadp.getSortMap(), this.cspadp.getMu());
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
