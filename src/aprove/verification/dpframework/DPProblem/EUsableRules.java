/*
 * Created on May 22, 2006
 */
package aprove.verification.dpframework.DPProblem;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * @author stein
 * @version $Id$
 *
 *
 * Implementation of usable rules and equations of EDP Framework.
 */

public class EUsableRules {

    protected static Logger logger = Logger.getLogger("aprove.verification.dpframework.DPProblem.EUsableRules");


    private final ETRSProblem etrs;

    private ImmutableSet<Rule> P; //current P
    private ImmutableSet<Equation> eSharp; //current eSharp
    private ImmutableSet<FunctionSymbol> delta; //current Delta
    private ImmutableSet<Rule> usableR; //current UsableRules
    private ImmutableSet<Equation> usableE; //current UsableE

    private ImmutableMap<Rule, QActiveCondition> activeRMap; //map from usable rules to QActiveConditions
    private ImmutableMap<Equation, QActiveCondition> activeEMap; //map from uzsable equations to QActiveConditions
    private SimpleGraph<FunctionSymbol, QActiveCondition> depGraph; //graph for calculating QActiveConditions
    private Map<FunctionSymbol, Node<FunctionSymbol>> nodeMap; //map from functionsymbols to corresponding nodes in depGraph

    public EUsableRules(ETRSProblem etrs) {
        this.etrs = etrs;
        this.P = null;
        this.eSharp = null;
        this.delta = null;
        this.usableR = null;
        this.usableE = null;
        this.depGraph = null;
        this.nodeMap = null;
        this.activeRMap = null;
        this.activeEMap = null;
    }

    private void initDepGraph(){
        Set<Node<FunctionSymbol>> nodes = new LinkedHashSet<Node<FunctionSymbol>>();
        this.nodeMap = new LinkedHashMap<FunctionSymbol, Node<FunctionSymbol>>();
        for (FunctionSymbol f : this.etrs.getDefinedSymbolsOfR()) {
            Node<FunctionSymbol> node = new Node<FunctionSymbol>(f);
            this.nodeMap.put(f, node);
            nodes.add(node);
        }
        for (FunctionSymbol f : this.etrs.getEquationMap().keySet()) {
            if(!this.nodeMap.keySet().contains(f)) {
                Node<FunctionSymbol> node = new Node<FunctionSymbol>(f);
                this.nodeMap.put(f, node);
                nodes.add(node);
            }
        }
        this.depGraph = new SimpleGraph<FunctionSymbol, QActiveCondition>(nodes);
    }


    /**
     * computes the usable rules for a given set of DPs, a set of Equations eSharp
     * and the underlying ETRS (which was passed in the constructor)
     */
    public ImmutableSet<Rule> getUsableRules(Collection<Rule> dps, Collection<Equation> eSharp) {
        if(Globals.useAssertions) {
            assert(this.etrs.checkNonCollapsingForE());
        }
        //only calculate if necessary
        if(this.delta == null || !this.P.equals(dps) || !this.eSharp.equals(eSharp)) {
            this.recalculateDeltaAndInitDepGraph(dps, eSharp);
            this.recalculateUsableEquations();
            this.recalculateUsableRules();
            this.recalculateActiveMaps(dps, eSharp, true);
            this.activeRMap = null;
            this.activeEMap = null;
        }
        return this.usableR;
    }

    /**
     * computes the usable rules for a given set of DPs, a set of Equations eSharp, a corresponding Afs
     * and the underlying ETRS (which was passed in the constructor)
     */
    public Set<Rule> getUsableRules(Collection<Rule> dps, Collection<Equation> eSharp, final QActiveCondition.Afs afs) {

        ImmutableMap<Rule, QActiveCondition> ruleMap = this.getQActiveConditionsForRules(dps, eSharp);
        Set<Rule> rules = new HashSet<Rule>();

        for(Map.Entry<Rule, QActiveCondition> e:ruleMap.entrySet()) {
            if(e.getValue().specialize(afs).isSatisfiable()) {
                rules.add(e.getKey());
            }
        }

        return ImmutableCreator.create(rules);
    }


    /**
     * computes the usable equations for a given set of DPs, a set of Equations eSharp
     * and the underlying ETRS (which was passed in the constructor)
     */
    public ImmutableSet<Equation> getUsableEquations(Collection<Rule> dps, Collection<Equation> eSharp) {
        if(Globals.useAssertions) {
            assert(this.etrs.checkNonCollapsingForE());
        }

        //      only calculate if necessary
        if(this.delta == null || !this.P.equals(dps) || !this.eSharp.equals(eSharp)) {
            this.recalculateDeltaAndInitDepGraph(dps, eSharp);
            this.recalculateUsableEquations();
            this.recalculateUsableRules();
            this.activeRMap = null;
            this.activeEMap = null;
        }
        return this.usableE;
    }

    /**
     * computes the usable equations for a given set of DPs, a set of Equations eSharp, a corresponding Afs
     * and the underlying ETRS (which was passed in the constructor)
     */
    public Set<Equation> getUsableEquations(Collection<Rule> dps, Collection<Equation> eSharp, final QActiveCondition.Afs afs) {

        ImmutableMap<Equation, QActiveCondition> eqMap = this.getQActiveConditionsForEquations(dps, eSharp);
        Set<Equation> eqs = new HashSet<Equation>();

        for(Map.Entry<Equation, QActiveCondition> e: eqMap.entrySet()) {
            if(e.getValue().specialize(afs).isSatisfiable()) {
                eqs.add(e.getKey());
            }
        }

        return ImmutableCreator.create(eqs);
    }

    /**
     * computes the activeconditions for the usable rules, with respect to the given values without using mergemutual
     */
    public ImmutableMap<Rule, QActiveCondition> getQActiveConditionsForRules(Collection<Rule> dps, Collection<Equation> eSharp) {
        return this.getQActiveConditionsForRules(dps, eSharp, false);
    }

    /**
     * computes the activeconditions for the usable rules, with respect to the given values
     */
    public ImmutableMap<Rule, QActiveCondition> getQActiveConditionsForRules(Collection<Rule> dps, Collection<Equation> eSharp,
            boolean mergemutual) {
        if(Globals.useAssertions) {
            assert(this.etrs.checkNonCollapsingForE());
        }

        //      only calculate if necessary
        if(this.delta == null || !this.P.equals(dps) || !this.eSharp.equals(eSharp) || this.activeRMap == null) {
            this.recalculateDeltaAndInitDepGraph(dps, eSharp);
            this.recalculateUsableEquations();
            this.recalculateUsableRules();
            this.recalculateActiveMaps(dps, eSharp, mergemutual);
        }
        return this.activeRMap;
    }

    /**
     * transforms a given set of rules to pseudo active usable rules
     * (where all conditions are TRUE, so in fact there is no active)
     */
    public static ImmutableMap<Rule, QActiveCondition> getRulesAsConditionMap(Set<Rule> rules) {
        Map<Rule, QActiveCondition> result = new LinkedHashMap<Rule, QActiveCondition>(rules.size());
        for (Rule rule : rules) {
            result.put(rule, QActiveCondition.TRUE);
        }
        return ImmutableCreator.create(result);
    }

    /**
     * computes the activeconditions for the usable rules, with respect to the given values without using mergemutual
     */
    public ImmutableMap<Equation, QActiveCondition> getQActiveConditionsForEquations(Collection<Rule> dps, Collection<Equation> eSharp) {
        return this.getQActiveConditionsForEquations(dps, eSharp, false);
    }

    /**
     * computes the activeconditions for the usable equations, with respect to the given values
     */
    public ImmutableMap<Equation, QActiveCondition> getQActiveConditionsForEquations(Collection<Rule> dps, Collection<Equation> eSharp,
            boolean mergemutual) {
        if(Globals.useAssertions) {
            assert(this.etrs.checkNonCollapsingForE());
        }

        //      only calculate if necessary
        if(this.delta == null || !this.P.equals(dps) || !this.eSharp.equals(eSharp) || this.activeEMap == null) {
            this.recalculateDeltaAndInitDepGraph(dps, eSharp);
            this.recalculateUsableEquations();
            this.recalculateUsableRules();
            this.recalculateActiveMaps(dps, eSharp, mergemutual);
        }
        this.recalculateActiveMaps(dps, eSharp, mergemutual);
        return this.activeEMap;

    }

    /**
     * transforms a given set of equations to pseudo active usable equations
     * (where all conditions are TRUE, so in fact there is no active)
     */
    public static ImmutableMap<Equation, QActiveCondition> getEquationsAsConditionMap(Set<Equation> eqs) {
        Map<Equation, QActiveCondition> result = new LinkedHashMap<Equation, QActiveCondition>(eqs.size());
        for (Equation eq : eqs) {
            result.put(eq, QActiveCondition.TRUE);
        }
        return ImmutableCreator.create(result);
    }


    /**
     * Calculates the current delta for the given DPs, eSharp and the underlying ETRS and
     * sets the current P and eSharp.
     */
    private void recalculateDeltaAndInitDepGraph(Collection<Rule> dps, Collection<Equation> eSharp) {
        this.initDepGraph();

        Set<FunctionSymbol> delta = new HashSet<FunctionSymbol>();
        Set<Rule> P = new HashSet<Rule>();
        for(Rule r:dps) {
            for(FunctionSymbol f:r.getRight().getFunctionSymbols()) {
                this.addToDelta(f, delta);
            }
            P.add(r);
        }
        Set<Equation> eS = new HashSet<Equation>();
        for(Equation es:eSharp) {
            for(FunctionSymbol f:es.getFunctionSymbols()) {
                this.addToDelta(f, delta);
            }
            eS.add(es);
        }

        this.delta = ImmutableCreator.create(delta);
        this.P = ImmutableCreator.create(P);
        this.eSharp = ImmutableCreator.create(eS);
        EUsableRules.logger.log(Level.FINE,"Calculated Delta of Usable Rules/Equations: \n"+this.delta.toString()+"\n");
    }

    private void addToDelta(FunctionSymbol f, Set<FunctionSymbol> delta) {
        if(!delta.contains(f)) {
            delta.add(f);
            if(this.etrs.getRuleMap().get(f) != null) {
                for (Rule r:this.etrs.getRuleMap().get(f)) {
                    for(FunctionSymbol fs:r.getRight().getFunctionSymbols()) {
                        this.addToDelta(fs, delta);
                    }
                    this.addAllEdges(f,r.getRight());
                }
            }
            if(this.etrs.getEquationMap().get(f) != null) {
                for (Equation e:this.etrs.getEquationMap().get(f)) {
                    if(((TRSFunctionApplication)e.getRight()).getRootSymbol().equals(f)) {
                        for(FunctionSymbol fs:e.getLeft().getFunctionSymbols()) {
                            this.addToDelta(fs, delta);
                        }
                        this.addAllEdges(f,e.getLeft());
                    }
                    if(((TRSFunctionApplication)e.getLeft()).getRootSymbol().equals(f)) {
                        for(FunctionSymbol fs:e.getRight().getFunctionSymbols()) {
                            this.addToDelta(fs, delta);
                        }
                        this.addAllEdges(f,e.getLeft());
                    }
                }
            }
        }
    }

    /**
     * Adds all edges with corresponding labeling from f to all defined functionsymbols of arguments of r
     */
    private void addAllEdges(FunctionSymbol f, TRSTerm r) {
        if(!r.isVariable()){
            TRSFunctionApplication rfa = (TRSFunctionApplication)r;

            FunctionSymbol root = rfa.getRootSymbol();
            if(this.isDefined(root)) {
                this.addEdge(this.nodeMap.get(f), this.nodeMap.get(root),QActiveCondition.TRUE );
            }

            int pos = 0;
            for(TRSTerm t:rfa.getArguments()) {
                if(!t.isVariable()) {
                    TRSFunctionApplication tfa = (TRSFunctionApplication)t;
                    this.addAllEdges(f,tfa,QActiveCondition.TRUE.and(rfa.getRootSymbol(),pos));
                }
                pos++;
            }
        }
    }

    private boolean isDefined(FunctionSymbol f) {
        return this.nodeMap.keySet().contains(f);
    }

    /**
     * Adds all edges with corresponding labeling (conjunctively combined
     * with c) from f to all defined functionsymbols of fa
     */
    private void addAllEdges(FunctionSymbol f, TRSFunctionApplication fa, QActiveCondition c) {
        FunctionSymbol root = fa.getRootSymbol();
        if(this.isDefined(root)) {
            this.addEdge(this.nodeMap.get(f), this.nodeMap.get(root),c);
        }
        int pos = 0;
        for(TRSTerm t:fa.getArguments()) {
            if(!t.isVariable()) {
                TRSFunctionApplication tfa = (TRSFunctionApplication)t;
                this.addAllEdges(f,tfa,c.and(fa.getRootSymbol(),pos));
            }
            pos++;
        }
    }

    /**
     * recalucaltes this.activeRMap and this.activeEMap
     */
    private void recalculateActiveMaps(Collection<Rule> dps, Collection<Equation> eSharp, boolean mergeMutual) {

        Map<Node<FunctionSymbol>, QActiveCondition> state = this.calculateDepGraphLabels(dps, eSharp, mergeMutual);

        // accumulate results
        Map<Rule, QActiveCondition> activeRMap = new LinkedHashMap<Rule, QActiveCondition>();
        Set<Rule> usableRules = new HashSet<Rule>(this.usableR);
        Iterator<Rule> it = usableRules.iterator();

        for (Map.Entry<Node<FunctionSymbol>, QActiveCondition> entry : state.entrySet()) {
            QActiveCondition condition = entry.getValue();
            FunctionSymbol f = entry.getKey().getObject();

            while (it.hasNext()) {
                Rule rule = it.next();
                if(rule.getLeft().getRootSymbol().equals(f)) {
                    activeRMap.put(rule, condition);
                    it.remove();
                }
            }
            it = usableRules.iterator();
        }

        Map<Equation, QActiveCondition> activeEMap = new LinkedHashMap<Equation, QActiveCondition>();
        Set<Equation> usableEquations = new HashSet<Equation>(this.usableE);
        Iterator<Equation> its = usableEquations.iterator();

        for (Map.Entry<Node<FunctionSymbol>, QActiveCondition> entry : state.entrySet()) {
            QActiveCondition condition = entry.getValue();
            FunctionSymbol f = entry.getKey().getObject();

            while (its.hasNext()) {
                Equation equation = its.next();
                if(!equation.getLeft().isVariable() && ((TRSFunctionApplication)equation.getLeft()).getRootSymbol().equals(f)) {
                    activeEMap.put(equation, condition);
                    its.remove();
                }
            }
            its = usableEquations.iterator();
        }
        //the same in symmetric version
        usableEquations = new HashSet<Equation>(this.usableE);
        its = usableEquations.iterator();

        for (Map.Entry<Node<FunctionSymbol>, QActiveCondition> entry : state.entrySet()) {
            QActiveCondition condition = entry.getValue();
            FunctionSymbol f = entry.getKey().getObject();

            while (its.hasNext()) {
                Equation equation = its.next();
                if(!equation.getRight().isVariable() && ((TRSFunctionApplication)equation.getRight()).getRootSymbol().equals(f)) {
                    if(activeEMap.containsKey(equation)) {
                        activeEMap.put(equation, condition.or(activeEMap.get(equation)));
                    }
                    else {
                        activeEMap.put(equation, condition);
                    }
                    its.remove();
                }
            }
            its = usableEquations.iterator();
        }

        this.activeRMap = ImmutableCreator.create(activeRMap);
        this.activeEMap = ImmutableCreator.create(activeEMap);
    }

    /**
     * recalculates the edges of depGraph, i.e. the activceConditions corresponding to current dps and eSharp
     */
    private Map<Node<FunctionSymbol>, QActiveCondition> calculateDepGraphLabels(Collection<Rule> dps, Collection<Equation> eSharp, boolean mergeMutual) {

        Set<Integer> todo = new TreeSet<Integer>(new Comparator<Integer>() {
            @Override
            public int compare(Integer arg0, Integer arg1) { return arg1.compareTo(arg0); }
        });  // traverse in reverse order to get high Sccs first!

        Map<Node<FunctionSymbol>, QActiveCondition> state = new HashMap<Node<FunctionSymbol>, QActiveCondition>(dps.size() + 10);

        // compute sccs and make lookup map for node->#scc and #scc -> scc
        // moreover, propagate qrNormal values
        Integer m = 0;
        Map<Integer,Cycle<FunctionSymbol>> nrToScc = new HashMap<Integer, Cycle<FunctionSymbol>>();
        Map<Node<FunctionSymbol>,Integer> nodeToSccNr = new HashMap<Node<FunctionSymbol>, Integer>();
        for (Cycle<FunctionSymbol> scc : this.depGraph.getSCCs(false)) {
           nrToScc.put(m, scc);
           for (Node<FunctionSymbol> node : scc) {
               nodeToSccNr.put(node, m);
           }
           m++;
        }


        // initially label every node reachable from DPs and eSharps
        for(Rule dp:dps) {
            if(!dp.getRight().isVariable()) {
                TRSFunctionApplication r = (TRSFunctionApplication)dp.getRight();
                int pos = 0;
                for(TRSTerm t:r.getArguments()) {
                    if(!t.isVariable()) {
                        TRSFunctionApplication tfa = (TRSFunctionApplication)t;
                        this.addAllInitialLabels(tfa,QActiveCondition.TRUE.and(r.getRootSymbol(),pos), state, todo, nodeToSccNr);
                    }
                    pos++;
                }
            }
        }
        for(Equation eq:eSharp) {
            if(!eq.getRight().isVariable()) {
                TRSFunctionApplication r = (TRSFunctionApplication)eq.getRight();
                int pos = 0;
                for(TRSTerm t:r.getArguments()) {
                    if(!t.isVariable()) {
                        TRSFunctionApplication tfa = (TRSFunctionApplication)t;
                        this.addAllInitialLabels(tfa,QActiveCondition.TRUE.and(r.getRootSymbol(),pos), state, todo, nodeToSccNr);
                    }
                    pos++;
                }
            }
            if(!eq.getLeft().isVariable()) {
                TRSFunctionApplication l = (TRSFunctionApplication)eq.getLeft();
                int pos = 0;
                for(TRSTerm t:l.getArguments()) {
                    if(!t.isVariable()) {
                        TRSFunctionApplication tfa = (TRSFunctionApplication)t;
                        this.addAllInitialLabels(tfa,QActiveCondition.TRUE.and(l.getRootSymbol(),pos), state, todo, nodeToSccNr);
                    }
                    pos++;
                }
            }
        }


        // then start labeling in order of the sccs
        Iterator<Integer> it = todo.iterator();
        while (it.hasNext()) {
            Integer nr = it.next();
            it.remove();
            Cycle<FunctionSymbol> scc = nrToScc.get(nr);
            int n = scc.size();
            if (mergeMutual || n == 1) {
                QActiveCondition cond = null;
                for (Node<FunctionSymbol> node : scc) {
                    QActiveCondition curr = state.get(node);
                    if (curr != null) {
                        if (cond == null) {
                            cond = curr;
                        } else {
                            cond = cond.or(curr);
                        }
                    }
                }
                // now we have the merged condition in cond
                // lets store this and propagate it down
                for (Node<FunctionSymbol> node : scc) {
                    state.put(node, cond);
                    for (Edge<QActiveCondition, FunctionSymbol> edge : this.depGraph.getOutEdges(node)) {
                        Node<FunctionSymbol> succ = edge.getEndNode();
                        Integer succNr = nodeToSccNr.get(succ);
                        // only look at edges out of current scc
                        if (!succNr.equals(nr)) {
                            todo.add(succNr);
                            QActiveCondition succCond = state.get(succ);
                            if (succCond == null) {
                                state.put(succ, cond.and(edge.getObject()));
                            } else {
                                state.put(succ, succCond.or(cond.and(edge.getObject())));
                            }
                        }
                    }
                }
            } else {

                // okay, we have to propagate conditions inside the scc
                // at most n-1 times
                // and we can end if there are no changes any more


                // a set where we store which node can propagate new values
                Set<Node<FunctionSymbol>> toIterate = new LinkedHashSet<Node<FunctionSymbol>>(n);
                Set<Node<FunctionSymbol>> nextToIterate = new LinkedHashSet<Node<FunctionSymbol>>(n);

                // in the first round we do not have to propagate null values
                for (Node<FunctionSymbol> node : scc) {
                    if (state.get(node) != null) {
                        toIterate.add(node);
                    }
                }

                for (int i=0; i<n; i++) {

                    for (Node<FunctionSymbol> node : toIterate) {
                        QActiveCondition cond = state.get(node);
                        for (Edge<QActiveCondition, FunctionSymbol> edge : this.depGraph.getOutEdges(node)) {
                            Node<FunctionSymbol> succ = edge.getEndNode();
                            Integer succNr = nodeToSccNr.get(succ);
                            // only look at edges in the current scc
                            if (succNr.equals(nr)) {
                                QActiveCondition succCond = state.get(succ);
                                if (succCond == null) {
                                    state.put(succ, cond.and(edge.getObject()));
                                    nextToIterate.add(succ);
                                } else {
                                    QActiveCondition newCond = succCond.or(cond.and(edge.getObject()));
                                    if (!newCond.equals(succCond)) {
                                        state.put(succ, newCond);
                                        nextToIterate.add(succ);
                                    }
                                }
                            }
                        }
                    }

                    if (nextToIterate.isEmpty()) {
                        break;
                    }
                    Set<Node<FunctionSymbol>> tmp = toIterate;
                    toIterate = nextToIterate;
                    nextToIterate = tmp;
                    nextToIterate.clear();
                }

                // at this point all information is passed inside the scc
                // now we have to propagate this values downwards
                for (Node<FunctionSymbol> node : scc) {
                    QActiveCondition cond = state.get(node);
                    for (Edge<QActiveCondition, FunctionSymbol> edge : this.depGraph.getOutEdges(node)) {
                        Node<FunctionSymbol> succ = edge.getEndNode();
                        Integer succNr = nodeToSccNr.get(succ);
                        // only look at edges out of current scc
                        if (!succNr.equals(nr)) {
                            todo.add(succNr);
                            QActiveCondition succCond = state.get(succ);
                            if (succCond == null) {
                                state.put(succ, cond.and(edge.getObject()));
                            } else {
                                state.put(succ, succCond.or(cond.and(edge.getObject())));
                            }
                        }
                    }
                }

            }
            it = todo.iterator();
        }


        return state;
    }

    /**
     * Recursively adds initial labels to nodes corresponding to functionsymbols in fa
     */
    private void addAllInitialLabels(TRSFunctionApplication fa, QActiveCondition c, Map<Node<FunctionSymbol>, QActiveCondition> state,
            Set<Integer> todo, Map<Node<FunctionSymbol>,Integer> nodeToSccNr) {

        FunctionSymbol root = fa.getRootSymbol();

        if(this.isDefined(root)){
            QActiveCondition succCond = state.get(this.nodeMap.get(root));
            QActiveCondition edgeCond = c;
            QActiveCondition newCond;
            if (succCond == null) {
                newCond = edgeCond;
            } else {
                if (succCond != QActiveCondition.TRUE) {
                    newCond = succCond.or(edgeCond);
                } else {
                    newCond = succCond;
                }
            }
            state.put(this.nodeMap.get(root), newCond);
            todo.add(nodeToSccNr.get(this.nodeMap.get(root)));
        }

        //recursive call for arguments of fa
        int pos = 0;
        for(TRSTerm t:fa.getArguments()) {
            if(!t.isVariable()) {
                TRSFunctionApplication tfa = (TRSFunctionApplication)t;
                this.addAllInitialLabels(tfa,c.and(root,pos), state, todo, nodeToSccNr);
            }
            pos++;
        }
    }

    /**
     * Calculates the usable Rules for the underlying ETRS, delta, P and eSharp.
     */
    private void recalculateUsableRules() {
        Set<Rule> usableR = new HashSet<Rule>();
        for(FunctionSymbol f:this.delta) {
            if(this.etrs.getDefinedSymbolsOfR().contains(f)) {
                usableR.addAll(this.etrs.getRuleMap().get(f));
            }
        }
        this.usableR = ImmutableCreator.create(usableR);
    }

    /**
     * Calculates the usable Equations for the underlying ETRS, delta, P and eSharp.
     */
    private void recalculateUsableEquations() {
        Set<Equation> usableE = new HashSet<Equation>();
        for(FunctionSymbol f:this.delta) {
            if(this.etrs.getEquationMap().get(f) != null) {
                usableE.addAll(this.etrs.getEquationMap().get(f));
            }
        }
        this.usableE = ImmutableCreator.create(usableE);
    }

    private void addEdge(Node<FunctionSymbol> from, Node<FunctionSymbol> to, QActiveCondition cond) {
        if (from != to) {
            this.depGraph.mergeEdge(from, to, cond, EUsableRules.LABEL_OR_COMBINER);
        }
    }

    private static final BinaryOperation<QActiveCondition> LABEL_OR_COMBINER = new BinaryOperation<QActiveCondition>() {
        @Override
        public QActiveCondition combine(QActiveCondition one, QActiveCondition two) {
            return one.or(two);
        }
    };

}
