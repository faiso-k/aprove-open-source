// TODO This class is not ready for parallelizing but should be!
package aprove.verification.dpframework.DPProblem;

import java.util.*;

import aprove.*;
import aprove.runtime.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Interesting to know:
 * The usable rules graph may contain more rules than those that are
 * actually usable (only the rules that are reachable from DPs are
 * really usable).
 * Advantages: No need to build the graph again if the Usable Rules Processor
 * has been applied; a QUsableRules object may be shared between several
 * DP-problems that arose by SCC decomposition (-> dependency graph processor).
 *
 * @author thiemann
 * @version $Id$
 */
public class QUsableRules {



    private final QTRSProblem qtrs;
    private boolean innermost;
    private Map<Rule, Node<Set<Rule>>> ruleMap; // a mapping from rules to their nodes
    private Map<FunctionSymbol, ? extends Set<Rule>> R; // a mapping from function symbols to corresponding rules, repr. R
    private Map<FunctionSymbol, Collection<TRSFunctionApplication>> criticalTermsInQ; // a mapping from function symbols to lhss of Q \ lhs(R), if innermost and non-empty set.
                                                                                 // All with standard prefix vars
    private QTermSet Q;
    private Map<Rule, Pair<GeneralizedRule,Node<Set<Rule>>>> dpMap; // dp to capped dp (in third standard) and corresponding node
    private Map<Rule, TRSTerm> dpToCappedRminusOneU; // a mapping from dps to capped lhss wrt. to R^-1, only in termination case and only if R^-1 is non-collapsing
    private Map<Rule, Map<FunctionSymbol, Set<Rule>>> dpToUsedRminusOneST; // a mapping from dps to their usable rules ^ -1, only in innermost case
    private Map<Node<Set<Rule>>, Integer> nodeToSccNr; // a mapping from nodes to a scc-nr
    private Map<Node<Set<Rule>>, Boolean> nodeToQRNormal; // a mapping from nodes to qr-normal conditions; null, iff criticalTermsInQ is null iff all terms satisfy condition

    private Map<Integer, Cycle<Set<Rule>>> nrToScc; // and a mapping from the nr to the scc;
                                                    // here also singleton nodes with no edges are sccs!


    // a graph where the nodes are the rules in P u R
    // and there is an edge from one rule to another
    // if whenever the first rule is usable, and the
    // conditions in the label are true, then the
    // other rule is also usable
    SimpleGraph<Set<Rule>, QActiveCondition> depGraph;

    public QUsableRules(QTRSProblem qtrs) {
        this.qtrs = qtrs;
        this.init();
    }

    public QTRSProblem getUnderlyingQTRS() {
        return this.qtrs;
    }

    private void init() {
        if (this.depGraph == null) {
            this.R = this.qtrs.getRuleMap();
            this.Q = this.qtrs.getQ();
            this.innermost = this.qtrs.QsupersetOfLhsR();

            // compute qrNormal conditions
            if (this.innermost) {
                Collection<TRSFunctionApplication> critQTerms = new HashSet<TRSFunctionApplication>(this.Q.getTerms());
                for (Rule rule : this.qtrs.getR()) {
                    critQTerms.remove(rule.getLhsInStandardRepresentation());
                }

                if (critQTerms.isEmpty()) {
                    this.criticalTermsInQ = null; // if Q \ lhs(R) is empty, we are trivially qrNormal, as in termination case
                } else {
                    this.criticalTermsInQ = new HashMap<FunctionSymbol, Collection<TRSFunctionApplication>>();
                    this.nodeToQRNormal = new HashMap<Node<Set<Rule>>, Boolean>(this.qtrs.getR().size());
                    for (TRSFunctionApplication fterm : critQTerms) {
                        FunctionSymbol f = fterm.getRootSymbol();
                        Collection<TRSFunctionApplication> critQs = this.criticalTermsInQ.get(f);
                        if (critQs == null) {
                            critQs = new ArrayList<TRSFunctionApplication>(4);
                            this.criticalTermsInQ.put(f, critQs);
                        }
                        critQs.add(fterm);
                    }
                }
            } else {
                // in termination case Q supset lhs(R) is not satisfied, hence qrNormal is trivially satisfied
                this.criticalTermsInQ = null;
            }

            // now construct the graph
            this.ruleMap = new LinkedHashMap<Rule, Node<Set<Rule>>>();
            Set<Node<Set<Rule>>> nodes = new LinkedHashSet<Node<Set<Rule>>>();
            for (Rule rule : this.qtrs.getR()) {
                Set<Rule> ruleSet = new LinkedHashSet<Rule>(1);
                ruleSet.add(rule);
                Node<Set<Rule>> node = new Node<Set<Rule>>(ruleSet);
                nodes.add(node);
                this.ruleMap.put(rule, node);
            }

            this.depGraph = new SimpleGraph<Set<Rule>, QActiveCondition>(nodes);

            // now compute all (non-recursive) usable rules and q
            for (Node<Set<Rule>> node : nodes) {
                Boolean qrNormal = this.criticalTermsInQ != null; // if we trivially satisfy the check, then do no check
                Rule rule = node.getObject().iterator().next().getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
                qrNormal = this.addInitialEdges(node, rule.getLeft(), rule.getRight(), 0, QActiveCondition.TRUE, qrNormal).z;
                // okay, in the trivial case set the proper value
                if (this.criticalTermsInQ != null) {
                    // store qrNormalValue
                    this.nodeToQRNormal.put(node, qrNormal);
                }
            }

            // merge nodes that are combined
            for (Cycle<Set<Rule>> scc : this.depGraph.getSCCs(QUsableRules.TRUE_FILTER)) {
                this.mergeRuleNodes(scc);
            }

            // compute sccs and make lookup map for node->#scc and #scc -> scc
            // moreover, propagate qrNormal values
            Integer n = 0;
            this.nrToScc = new HashMap<Integer, Cycle<Set<Rule>>>();
            this.nodeToSccNr = new HashMap<Node<Set<Rule>>, Integer>(this.R.size());
            for (Cycle<Set<Rule>> scc : this.depGraph.getSCCs(false)) {
               this.nrToScc.put(n, scc);
               if (this.nodeToQRNormal == null) {
                   // no propagation of qr-Normal values here
                   for (Node<Set<Rule>> node : scc) {
                       this.nodeToSccNr.put(node, n);
                   }
               } else {
                   boolean qrNormal = true;
                   for (Node<Set<Rule>> node : scc) {
                       this.nodeToSccNr.put(node, n);
                       if (qrNormal) {
                           qrNormal = this.nodeToQRNormal.get(node).booleanValue();
                       }
                   }

                   if (!qrNormal) {
                       for (Node<Set<Rule>> node : scc) {
                           for (Node<Set<Rule>> pred : this.depGraph.getIn(node)) {
                               this.nodeToQRNormal.put(pred, Boolean.FALSE);
                           }
                       }
                   }

               }

               n++;
            }

            // create lookup maps for dps
            this.dpMap = new HashMap<Rule, Pair<GeneralizedRule,Node<Set<Rule>>>>();
            if (this.innermost) {
                this.dpToUsedRminusOneST = new HashMap<Rule, Map<FunctionSymbol, Set<Rule>>>();
            } else {
                if (!this.qtrs.isCollapsing()) {
                    this.dpToCappedRminusOneU = new HashMap<Rule, TRSTerm>();
                }
            }


        }
    }

    private void mergeRuleNodes(Set<Node<Set<Rule>>> toMerge) {
        Node<Set<Rule>> collapsed = this.depGraph.merge(toMerge, QUsableRules.NODE_UNION_COMBINER, QUsableRules.LABEL_OR_COMBINER);
        final boolean nonTrivial = this.criticalTermsInQ != null;
        boolean qrNormal = nonTrivial;
        for (Node<Set<Rule>> node : toMerge) {
            for (Rule rule : node.getObject()) {
                this.ruleMap.put(rule, collapsed);
                if (qrNormal) {
                    qrNormal = this.nodeToQRNormal.get(node).booleanValue();
                }
            }
        }

        // store new qrNormal value if needed
        // (if qrNormal was true, then all nodes have true in the end, nothing to change)
        if (nonTrivial && !qrNormal) {
            this.nodeToQRNormal.put(collapsed, Boolean.FALSE);
        }

        this.depGraph.removeEdge(collapsed, collapsed);
    }

    /**
     * returns a possibly new map of rules to specialized active conditions w.r.t. the AFS.
     * Rules with unsatisfiable active conditions have been thrown out.
     * @param rules
     * @param afs
     * @return
     */
    public static Map<Rule, QActiveCondition> getSpecializedActiveConditions(Map<Rule, QActiveCondition> rules, QActiveCondition.Afs afs) {
        Map<QActiveCondition, QActiveCondition> newConditions = new HashMap<QActiveCondition, QActiveCondition>();
        boolean changed = false;
        Iterator<Map.Entry<Rule, QActiveCondition>> rulesIt = rules.entrySet().iterator();
        while (rulesIt.hasNext()) {
            Map.Entry<Rule, QActiveCondition> rule = rulesIt.next();
            QActiveCondition cond = rule.getValue();
            QActiveCondition newCond = newConditions.get(cond);
            if (newCond == null) {
                // we have to compute the new condition
                newCond = cond.specialize(afs);
                newConditions.put(cond, newCond);
                // okay, we have to change something
                if (newCond != cond) {
                    // if this is the first change, create a new map
                    if (!changed) {
                        changed = true;
                        SortedMap<Rule, QActiveCondition> newRules = new TreeMap<Rule, QActiveCondition>(rules);
                        rules = newRules;
                        rulesIt = newRules.tailMap(rule.getKey()).entrySet().iterator();
                        rule = rulesIt.next();
                    }

                    // and set the new value
                    if (!newCond.isSatisfiable()) {
                        rulesIt.remove();
                    } else {
                        rule.setValue(newCond);
                    }

                }
            } else {
                if (cond != newCond) {
                    if (!newCond.isSatisfiable()) {
                        rulesIt.remove();
                    } else {
                        rule.setValue(newCond);
                    }
                }
            }
        }
        return rules;
    }

    /**
     * computes the active condition for each DP. This is done by labeling
     * the usable rules graph with boolean conditions and propogate these
     * values accordingly.
     * @param dps
     * @return
     */
    public Map<Rule, QActiveCondition> getActiveConditions(Set<Rule> dps) {
        return this.getActiveConditions(dps, false);
    }

    /**
     * computes the active condition for each DP. This is done by labeling
     * the usable rules graph with boolean conditions and propogate these
     * values accordingly.
     * @param dps
     * @param mergeMutual if true, then mutual recursive rules obtain one shared active condition
     * @return
     */
    public Map<Rule, QActiveCondition> getActiveConditions(Set<Rule> dps, boolean mergeMutual) {
        //init();

        Set<Node<Set<Rule>>> dpNodes = this.addDPs(dps);
        Set<Integer> todo = new TreeSet<Integer>(new Comparator<Integer>() {
            @Override
            public int compare(Integer arg0, Integer arg1) { return arg1.compareTo(arg0); }
        });  // traverse in reverse order to get high Sccs first!

        Map<Node<Set<Rule>>, QActiveCondition> state = new LinkedHashMap<Node<Set<Rule>>, QActiveCondition>(dps.size() + 10);

        // initially label every node reachable from DPs
        for (Node<Set<Rule>> dpNode : dpNodes) {
            for (Edge<QActiveCondition, Set<Rule>> edge :  this.depGraph.getOutEdges(dpNode)) {
                Node<Set<Rule>> successor = edge.getEndNode();
                QActiveCondition succCond = state.get(successor);
                QActiveCondition edgeCond = edge.getObject();
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
                state.put(successor, newCond);
                todo.add(this.nodeToSccNr.get(successor));
            }
        }


        // then start labeling in order of the sccs
        Iterator<Integer> it = todo.iterator();
        while (it.hasNext()) {
            Integer nr = it.next();
            it.remove();
            Cycle<Set<Rule>> scc = this.nrToScc.get(nr);
            int n = scc.size();
            if (mergeMutual || n == 1) {
                QActiveCondition cond = null;
                for (Node<Set<Rule>> node : scc) {
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
                for (Node<Set<Rule>> node : scc) {
                    state.put(node, cond);
                    for (Edge<QActiveCondition, Set<Rule>> edge : this.depGraph.getOutEdges(node)) {
                        Node<Set<Rule>> succ = edge.getEndNode();
                        Integer succNr = this.nodeToSccNr.get(succ);
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
                Set<Node<Set<Rule>>> toIterate = new LinkedHashSet<Node<Set<Rule>>>(n);
                Set<Node<Set<Rule>>> nextToIterate = new LinkedHashSet<Node<Set<Rule>>>(n);

                // in the first round we do not have to propagate null values
                for (Node<Set<Rule>> node : scc) {
                    if (state.get(node) != null) {
                        toIterate.add(node);
                    }
                }

                for (int i=0; i<n; i++) {

                    for (Node<Set<Rule>> node : toIterate) {
                        QActiveCondition cond = state.get(node);
                        for (Edge<QActiveCondition, Set<Rule>> edge : this.depGraph.getOutEdges(node)) {
                            Node<Set<Rule>> succ = edge.getEndNode();
                            Integer succNr = this.nodeToSccNr.get(succ);
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
                    Set<Node<Set<Rule>>> tmp = toIterate;
                    toIterate = nextToIterate;
                    nextToIterate = tmp;
                    nextToIterate.clear();
                }

                // at this point all information is passed inside the scc
                // now we have to propagate this values downwards
                for (Node<Set<Rule>> node : scc) {
                    QActiveCondition cond = state.get(node);
                    for (Edge<QActiveCondition, Set<Rule>> edge : this.depGraph.getOutEdges(node)) {
                        Node<Set<Rule>> succ = edge.getEndNode();
                        Integer succNr = this.nodeToSccNr.get(succ);
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

        // accumulate results
        Map<Rule, QActiveCondition> result = new LinkedHashMap<Rule, QActiveCondition>();
        for (Map.Entry<Node<Set<Rule>>, QActiveCondition> entry : state.entrySet()) {
            QActiveCondition condition = entry.getValue();
            for (Rule rule : entry.getKey().getObject()) {
                result.put(rule, condition);
            }
        }


        return result;
    }

    /**
     * computes the usable rules for a given DP and
     * the underlying QTRS (which was passed in the constructor)
     * @param dp
     * @return the set of usable rules, this set may be modified.
     */
    public Set<Rule> getUsableRules(Rule dp) {
        ArrayList<Rule> theDp = new ArrayList<Rule>(1);
        theDp.add(dp);
        return this.getUsableRules(theDp);
    }

    /**
     * computes whether there is at least one usable rule for a given DP and
     * the underlying QTRS (which was passed in the constructor)
     * @param dp
     * @return true iff the usable rules for this dp are non-empty
     */
    public boolean hasUsableRules(Rule dp) {
        //init();
        Node<Set<Rule>> node = this.addDP(dp).y;
        return !this.depGraph.getOut(node).isEmpty();
    }


    /**
     * computes the usable rules for a given set of DPs and
     * the underlying QTRS (which was passed in the constructor)
     * @param dps
     * @return the set of usable rules, this set may be modified.
     */
    public Set<Rule> getUsableRules(Collection<Rule> dps) {
        return this.getUsableRules(dps, null);
    }



    /**
     * computes the usable rules for a given set of DPs, a corresponding Afs,
     * and the underlying QTRS (which was passed in the constructor)
     * @param dps
     * @param afs
     * @return the set of usable rules, this set may be modified.
     */
    public Set<Rule> getUsableRules(Collection<Rule> dps, final QActiveCondition.Afs afs) {
        //init();
        Set<Node<Set<Rule>>> nodesForDPs = this.addDPs(dps);
        Set<Node<Set<Rule>>> reachable;
        if (afs == null) {
            reachable = this.depGraph.determineReachableNodes(nodesForDPs);
        } else {
            EdgeFilter<QActiveCondition,Set<Rule>> filter = new EdgeFilter<QActiveCondition, Set<Rule>>() {
                @Override
                public boolean selectEdge(Node<Set<Rule>> source, Node<Set<Rule>> dest, QActiveCondition label) {
                    return label.specialize(afs).isSatisfiable();
                }
            };
            reachable = this.depGraph.determineReachableNodes(nodesForDPs, filter);
        }
        Set<Rule> usable = new LinkedHashSet<Rule>();
        for (Node<Set<Rule>> node : reachable) {
            // add rules only of rule nodes!
            if (!nodesForDPs.contains(node)) {
                usable.addAll(node.getObject());
            }
        }

        return usable;
    }

    /**
     * computes whether the dp satisfies the qr-Normal condition
     * @param dp
     */
    public boolean getQRNormal(Rule dp) {
        //init();
        if (this.nodeToQRNormal == null) {
            return true;
        } else {
            Node<Set<Rule>> n = this.addDP(dp).y;
            return this.nodeToQRNormal.get(n).booleanValue();
        }
    }

    /**
     * computes whether all dps satisfy the qr-Normal condition
     * @param dps
     */
    public boolean getQRNormal(Iterable<? extends Rule> dps) {
        //init();
        if (this.nodeToQRNormal == null) {
            return true;
        } else {
            for (Rule dp : dps) {
                Node<Set<Rule>> n = this.addDP(dp).y;
                boolean res = this.nodeToQRNormal.get(n).booleanValue();
                if (!res) {
                    return false;
                }
            }
            return true;
        }
    }



    /**
     * transforms a gives set of rules to pseudo active usable rules
     * (where all conditions are TRUE, so in fact there is no active)
     * @param rules
     * @return
     */
    public static Map<Rule, QActiveCondition> getRulesAsConditionMap(Collection<Rule> rules) {
        Map<Rule, QActiveCondition> result = new LinkedHashMap<Rule, QActiveCondition>(rules.size());
        for (Rule rule : rules) {
            result.put(rule, QActiveCondition.TRUE);
        }
        return result;
    }

    /**
     * adds the dps to the graph and
     * returns the corresponding set of nodes
     * @param dps
     * @return the set of nodes for the DPs, the set may be modified
     */
    private Set<Node<Set<Rule>>> addDPs(Collection<Rule> dps) {
        Set<Node<Set<Rule>>> res = new LinkedHashSet<Node<Set<Rule>>>(dps.size());
        for (Rule dp : dps) {
            res.add(this.addDP(dp).y);
        }
        return res;
    }

    /**
     * adds a dp to this calculator if not already added,
     * asserts that init() has been called before.
     * @param dp
     * @return the capped dp and the corresponding node
     */
    private synchronized Pair<GeneralizedRule,Node<Set<Rule>>> addDP(Rule dp) {
        Pair<GeneralizedRule, Node<Set<Rule>>> cap_and_node = this.dpMap.get(dp);
        if (cap_and_node == null) {
            Set<Rule> dpLabel = new HashSet<Rule>(1);
            dpLabel.add(dp);
            Node<Set<Rule>> n = new Node<Set<Rule>>(dpLabel);
            this.depGraph.addNode(n);
            dp = dp.getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
            boolean calcQRNormal = this.criticalTermsInQ != null;
            Triple<TRSTerm, Integer, Boolean> cap_t_and_qrNormal = this.addDPEdges(n, dp.getLeft(), dp.getRight(), 0, QActiveCondition.TRUE, calcQRNormal, this.innermost || !this.Q.canBeRewritten(dp.getLeft()));
            if (calcQRNormal) {
                this.nodeToQRNormal.put(n, cap_t_and_qrNormal.z);
            }
            cap_and_node = new Pair<GeneralizedRule, Node<Set<Rule>>>(GeneralizedRule.create(dp.getLeft(), cap_t_and_qrNormal.x), n);
            this.dpMap.put(dp, cap_and_node);
        }
        return cap_and_node;
    }


    /**
     * returns the capped dp
     * (where variables are only from 2. and 3. standard prefix)
     * Capping was done by renaming the dp to 3. prefix and introducing 2. prefix
     * @param dp
     * @return
     */
    public GeneralizedRule getCappedDP(Rule dp) {
        //init();
        return this.addDP(dp).x;
    }


    @Override
    public String toString() {
        //init();
        StringBuffer t = new StringBuffer("digraph dp_graph {\nnode [outthreshold=100, inthreshold=100];\n");
        for (Node<Set<Rule>> node : this.depGraph.getNodes()) {
            t.append(node.getNodeNumber()+" [");
            t.append("label=\"");
            boolean first = true;
            for (Rule rule : node.getObject()) {
                if (first) {
                    first = false;
                } else {
                    t.append("\\n");
                }
                t.append(rule.toString());
            }
            t.append("\", fontsize=16];\n");
        }
        for (Edge<QActiveCondition, Set<Rule>> edge : this.depGraph.getEdges()) {
            t.append(edge.getStartNode().getNodeNumber() + " -> "
                    + edge.getEndNode().getNodeNumber());
            t.append("[label=\"" + edge.getObject() + "\"];\n");
        }
        t.append("}\n");
        return t.toString();
    }

    /**
     * the method is very similar to <code>addInitialEdges</code>
     * @param fromNode draw edges from this node
     * @param s consider this term as lhs
     * @param t a subterm of the original rhs
     * @param nr the number for the next free var
     * @param cond the condition so far
     * @param qrNormal chance to satisfy qrNormal
     * @param sInQNF is s a Q-normal form or not (in innermost case this value may always be true, as a harder check is performed in this routine)
     * @return (cap_s(t),next nr for free var, qrNormal can be satisfied) where vars in cap_s(t) are from 2. and 3. prefix
     */
    private Triple<TRSTerm, Integer, Boolean> addDPEdges(Node<Set<Rule>> fromNode, TRSTerm s, TRSTerm t, Integer nr, QActiveCondition cond, Boolean qrNormal, final boolean sInQNF) {
        if (Globals.useAssertions) {
            assert(t.checkVariablePrefix(TRSTerm.THIRD_STANDARD_PREFIX));
            assert(s.checkVariablePrefix(TRSTerm.THIRD_STANDARD_PREFIX));
        }

        if (t.isVariable()) {
            if (this.innermost) {
                return new Triple<TRSTerm, Integer, Boolean>(t, nr, qrNormal);
            } else {
                return new Triple<TRSTerm, Integer, Boolean>(TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX+"_"+nr), nr+1, qrNormal);
            }
        } else {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            FunctionSymbol f = ft.getRootSymbol();
            ImmutableList<? extends TRSTerm> args = ft.getArguments();
            List<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
            int i = 0;
            Integer oldNr = nr;
            for (TRSTerm arg : args) {
                QActiveCondition condArg = cond.and(f, i);
                Triple<TRSTerm, Integer, Boolean> argRes = this.addDPEdges(fromNode, s, arg, nr, condArg, qrNormal, sInQNF);
                newArgs.add(argRes.x);
                nr = argRes.y;
                qrNormal = argRes.z;
                i++;
            }
            if (!nr.equals(oldNr)) {
                ft = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(newArgs));
            }

            // now we have the term f(cap(t_1), ..., cap(t_n)) in ft
            // let us check which rules can be connected at top position
            boolean someConnection = false;
            Set<Rule> possibleRules = this.R.get(f);
            if (possibleRules != null && sInQNF) {
                for (Rule rule : possibleRules) {
                    TRSFunctionApplication l = rule.getLhsInStandardRepresentation();
                    boolean drawEdge;
                    if (this.innermost && !Options.certifier.isA3pat() && !Options.certifier.isRainbow()) {
                        TRSSubstitution sigma = ft.getMGU(l);
                        if (sigma == null) {
                            drawEdge = false;
                        } else {
                            drawEdge = !this.Q.canBeRewritten(s.applySubstitution(sigma)) &&
                                !this.Q.canBeRewrittenBelowRoot(l.applySubstitution(sigma));
                        }
                    } else {
                        drawEdge = Options.certifier.isA3pat() || Options.certifier.isRainbow() || ft.unifies(l); // a3pat and rainbow can only do EDG!
                    }
                    if (drawEdge) {
                        someConnection = true;
                        Node<Set<Rule>> ruleNode = this.ruleMap.get(rule);
                        // update qr-normal value from rules
                        if (qrNormal.booleanValue()) {
                            qrNormal = this.nodeToQRNormal.get(ruleNode);
                        }
                        this.addEdge(fromNode, ruleNode, cond);
                    }
                }
            }

            // and update qrNormal value for this term
            if (this.nodeToQRNormal != null && qrNormal.booleanValue()) {
                Collection<TRSFunctionApplication> critQs = this.criticalTermsInQ.get(f);
                if (critQs != null) {
                    for (TRSFunctionApplication critQ : critQs) {
                        if (critQ.unifies(ft)) {
                            qrNormal = Boolean.FALSE;
                            break;
                        }
                    }
                }
            }

            if (someConnection) {
                return new Triple<TRSTerm, Integer, Boolean>(TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX+"_"+nr), nr+1, qrNormal);
            } else {
                return new Triple<TRSTerm, Integer, Boolean>(ft, nr, qrNormal);
            }
        }
    }

    /**
     * computes cap_R^-1(u) (where vars are from 2. prefix). Note that this method
     * may only be called in termination case.
     * @param u_to_v a dp
     */
    public synchronized TRSTerm getCapRminusOneOfU(Rule u_to_v) {
        //init();
        if (this.dpToCappedRminusOneU == null) {
            return QUsableRules.Y;
        } else {
            TRSTerm capped = this.dpToCappedRminusOneU.get(u_to_v);
            if (capped == null) {
                capped = QUsableRules.computeCapRminusOne(u_to_v.getLeft(), 0, this.qtrs.getReverseRuleMap()).x;
                this.dpToCappedRminusOneU.put(u_to_v, capped);
            }
            return capped;
        }
    }

    private final static TRSVariable Y = TRSVariable.createVariable(TRSTerm.SECOND_STANDARD_PREFIX);

    /**
     * computes cap_U(s_to_t,R) (u) (where vars are from 2. prefix).
     * This method may only be called in the innermost case.
     * @param s_to_t
     * @param u_to_v
     * @return
     */
    public TRSTerm getCapUsedRminusOneOfU(Rule s_to_t, Rule u_to_v) {
        //init();
        Map<FunctionSymbol, Set<Rule>> usableRules;
        synchronized(this) {
            usableRules = this.dpToUsedRminusOneST.get(s_to_t);
            if (usableRules == null) {
                usableRules = Rule.getReversedRuleMap(this.getUsableRules(s_to_t));
                this.dpToUsedRminusOneST.put(s_to_t, usableRules);
            }
        }

        if (usableRules.get(null) != null) { // we have a collapsing usable rule
            return QUsableRules.Y;
        } else {
            return QUsableRules.computeCapRminusOne(u_to_v.getLeft(), 0, usableRules).x;
        }
    }

    /**
     * computes CapR^-1(t) where rMinusOne has to be non-Collapsing
     * @param t
     * @param nr
     * @param rMinusOne
     * @return the capped term and the next free var, where the capped term has vars from 2. prefix only
     */
    private static Pair<TRSTerm, Integer> computeCapRminusOne(TRSTerm t, Integer nr, Map<FunctionSymbol, ? extends Set<Rule>> rMinusOne) {
        if (Globals.useAssertions) {
            assert(rMinusOne.get(null) == null);
        }

        if (t.isVariable()) {
            return new Pair<TRSTerm, Integer>(TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX+"_"+nr), nr+1);
        } else {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            FunctionSymbol f = ft.getRootSymbol();
            ImmutableList<? extends TRSTerm> args = ft.getArguments();
            List<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
            int i = 0;
            Integer oldNr = nr;
            for (TRSTerm arg : args) {
                Pair<TRSTerm, Integer> argRes = QUsableRules.computeCapRminusOne(arg, nr, rMinusOne);
                newArgs.add(argRes.x);
                nr = argRes.y;
                i++;
            }
            if (!nr.equals(oldNr)) {
                ft = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(newArgs));
            }

            // now we have the term f(cap(t_1), ..., cap(t_n)) in ft
            // let us check whether some rule unifies at top position
            Set<Rule> possibleRules = rMinusOne.get(f);
            if (possibleRules != null) {
                for (Rule rule : possibleRules) {
                    TRSTerm r = rule.getRhsInStandardRepresentation();
                    if (ft.unifies(r)) {
                        return new Pair<TRSTerm, Integer>(TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX+"_"+nr), nr+1);
                    }
                }
            }

            return new Pair<TRSTerm, Integer>(ft, nr);
        }
    }


    /**
     * @param fromNode
     * @param l the lhs of a rule, with variables of THIRD_STANDARD_PREFIX
     * @param r a (part of) rhs of a rule (l -> C[r]), with variables of THIRD_STANDARD_PREFIX
     * @param nr the next free variable to be chosen
     * @param cond
     * @param qrNormal - have we a chance to satisfy qrNormal up to now?
     * @return the triple (cap(r), new_nr, qrnormal) where new_nr is the next free variable one can create,
     *         and qrnormal is true iff the input qrNormal is true and for the term r we
     *         have that every r does not conflict with the qr-implies-q-normal condition directly! (without tracking usable rules)
     *         The vars of cap(r) are from 2. and 3. prefix
     */
    private Triple<TRSTerm, Integer, Boolean> addInitialEdges(Node<Set<Rule>> fromNode, TRSTerm l, TRSTerm r, Integer nr, QActiveCondition cond, Boolean qrNormal) {
        if (Globals.useAssertions) {
            assert(l.checkVariablePrefix(TRSTerm.THIRD_STANDARD_PREFIX));
            assert(r.checkVariablePrefix(TRSTerm.THIRD_STANDARD_PREFIX));
        }
        if (r.isVariable()) {
            if (this.innermost) {
                return new Triple<TRSTerm, Integer, Boolean>(r, nr, qrNormal);
            } else {
                return new Triple<TRSTerm, Integer, Boolean>(TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX+"_"+nr), nr+1, qrNormal);
            }
        } else {
            TRSFunctionApplication fr = (TRSFunctionApplication) r;
            FunctionSymbol f = fr.getRootSymbol();
            ImmutableList<? extends TRSTerm> args = fr.getArguments();
            List<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
            int i = 0;
            Integer oldNr = nr;
            for (TRSTerm arg : args) {
                QActiveCondition condArg = cond.and(f, i);
                Triple<TRSTerm,Integer, Boolean> argRes = this.addInitialEdges(fromNode, l, arg, nr, condArg, qrNormal);
                newArgs.add(argRes.x);
                nr = argRes.y;
                qrNormal = argRes.z;
                i++;
            }
            if (!nr.equals(oldNr)) {
                fr = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(newArgs));
            }

            // now we have the term f(cap(r_1), ..., cap(r_n)) in fr (with second or third standard prefix vars only)
            // let us check which rules can be connected at top position
            boolean someConnection = false;
            Set<Rule> possibleRules = this.R.get(f);
            if (possibleRules != null) {
                for (Rule rule : possibleRules) {
                    TRSFunctionApplication ruleL = rule.getLhsInStandardRepresentation();
                    if (this.innermost) {
                        // do normal check for computation of cap!
                        TRSSubstitution sigma = fr.getMGU(ruleL);
                        if (sigma != null) {
                            if (!this.Q.canBeRewrittenBelowRoot(fr.applySubstitution(sigma))) {
                                if (!this.Q.canBeRewrittenBelowRoot(l.applySubstitution(sigma))) {
                                    someConnection = true;
                                    this.addEdge(fromNode, this.ruleMap.get(rule), cond);
                                }
                            }
                        }
                    } else {
                        if (fr.unifies(ruleL)) {
                            someConnection = true;
                            this.addEdge(fromNode, this.ruleMap.get(rule), cond);
                        }
                    }
                }
            }

            if (qrNormal.booleanValue()) {
                Collection<TRSFunctionApplication> critTerms = this.criticalTermsInQ.get(f);
                if (critTerms != null) {
                    for (TRSFunctionApplication critTerm : critTerms) {
                        if (critTerm.unifies(fr)) {
                            qrNormal = Boolean.FALSE;
                            break;
                        }
                    }
                }
            }

            if (someConnection) {
                return new Triple<TRSTerm, Integer, Boolean>(TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX+"_"+nr), nr+1, qrNormal);
            } else {
                return new Triple<TRSTerm, Integer, Boolean>(fr, nr, qrNormal);
            }
        }
    }



    private void addEdge(Node<Set<Rule>> from, Node<Set<Rule>> to, QActiveCondition cond) {
        if (from != to) {
            this.depGraph.mergeEdge(from, to, cond, QUsableRules.LABEL_OR_COMBINER);
        }
    }


    private static final BinaryOperation<Set<Rule>> NODE_UNION_COMBINER = new BinaryOperation<Set<Rule>>() {
        @Override
        public Set<Rule> combine(Set<Rule> one, Set<Rule> two) {
            one.addAll(two);
            return one;
        }
    };


    private final static EdgeFilter<QActiveCondition, Set<Rule>> TRUE_FILTER = new EdgeFilter<QActiveCondition, Set<Rule>>() {
        @Override
        public boolean selectEdge(Node<Set<Rule>> from, Node<Set<Rule>> to, QActiveCondition label) {
            return label == QActiveCondition.TRUE;
        }
    };


    private static final BinaryOperation<QActiveCondition> LABEL_OR_COMBINER = new BinaryOperation<QActiveCondition>() {
        @Override
        public QActiveCondition combine(QActiveCondition one, QActiveCondition two) {
            return one.or(two);
        }
    };

}
