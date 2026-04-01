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

public class CSPAUseable {

    private CSPADPProblem cspadp;

    private SimpleGraph<FunctionSymbol, Object> depGraph;
    private Map<FunctionSymbol, Node<FunctionSymbol>> nodeMap;

    public CSPAUseable(CSPADPProblem cspadp) {
        this.cspadp = cspadp;
        this.depGraph = null;
        this.nodeMap = null;
    }

    /**
     * Computes the usable CSPATRS for a given set of DPs.
     */
    public CSPATRSProblem getUseable(Collection<PARule> dps) {
        if (this.depGraph == null) {
            this.calcDepGraph();
        }
        return this.calcUseable(dps);
    }

    private void calcDepGraph() {
        Set<Node<FunctionSymbol>> nodes = new LinkedHashSet<Node<FunctionSymbol>>();
        this.nodeMap = new LinkedHashMap<FunctionSymbol, Node<FunctionSymbol>>();
        for (FunctionSymbol f : this.cspadp.getSignatureNoTuple()) {
            Node<FunctionSymbol> node = new Node<FunctionSymbol>(f);
            this.nodeMap.put(f, node);
            nodes.add(node);
        }
        this.depGraph = new SimpleGraph<FunctionSymbol, Object>(nodes);

        for (PARule rule : this.cspadp.getR()) {
            this.addDelta(rule.getLeft(), rule.getRight());
        }
    }

    private void addDelta(TRSTerm l, TRSTerm r) {
        if (!l.isVariable()) {
            this.addDelta(((TRSFunctionApplication) l).getRootSymbol(), l, r);
        }
    }

    private void addDelta(FunctionSymbol f, TRSTerm l, TRSTerm r) {
        Set<FunctionSymbol> funs = r.getFunctionSymbols();
        funs.addAll(this.getInactive(l, this.cspadp.getMu()));
        for (FunctionSymbol ff : funs) {
            this.addEdge(f, ff);
        }
    }

    private Set<FunctionSymbol> getInactive(TRSTerm l, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        Set<FunctionSymbol> res = new LinkedHashSet<FunctionSymbol>();
        for (TRSTerm t : CSTermHelper.getInactiveSubterms(l, mu)) {
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

    private CSPATRSProblem calcUseable(Collection<PARule> dps) {
        Set<FunctionSymbol> delta = new LinkedHashSet<FunctionSymbol>();
        for (PARule dp : dps) {
            Set<FunctionSymbol> dpfs = dp.getRight().getFunctionSymbols();
            dpfs.remove(((TRSFunctionApplication) dp.getRight()).getRootSymbol());
            delta.addAll(dpfs);
            delta.addAll(this.getInactive(dp.getLeft(), this.cspadp.getMu()));
        }
        for (PARule r : this.cspadp.getR()) {
            delta.addAll(this.getInactive(r.getRight(), this.cspadp.getMu()));
        }

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
        deltastar.addAll(this.cspadp.getSignatureSE());

        ImmutableSet<PARule> newR = ImmutableCreator.create(this.getR(this.cspadp.getR(), deltastar));
        ImmutableSet<Rule> newS = ImmutableCreator.create(this.getS(this.cspadp.getS(), deltastar));
        ImmutableSet<Equation> newE = ImmutableCreator.create(this.getE(this.cspadp.getE(), deltastar));
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
