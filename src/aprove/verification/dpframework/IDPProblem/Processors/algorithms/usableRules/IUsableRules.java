/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.cap.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class IUsableRules implements IUsableRulesEstimation {

    private final FunctionSymbol unmatchable;
    private final IDPRuleAnalysis ruleAnalysis;
    private boolean innermost;
    private Map<GeneralizedRule, Node<Set<GeneralizedRule>>> ruleMap; // a mapping from rules to their nodes
    private Map<FunctionSymbol, ? extends Set<GeneralizedRule>> R; // a mapping from function symbols to corresponding rules, repr. R
    private Map<FunctionSymbol, Collection<TRSFunctionApplication>> criticalTermsInQ; // a mapping from function symbols to lhss of Q \ lhs(R), if innermost and non-empty set.
                                                                                 // All with standard prefix vars
    private IQTermSet Q;
    private Map<GeneralizedRule, Pair<GeneralizedRule,Node<Set<GeneralizedRule>>>> dpMap; // dp to capped dp (in third standard) and corresponding node
    private Map<Node<Set<GeneralizedRule>>, Integer> nodeToSccNr; // a mapping from nodes to a scc-nr
    private Map<Node<Set<GeneralizedRule>>, Boolean> nodeToQRNormal; // a mapping from nodes to qr-normal conditions; null, iff criticalTermsInQ is null iff all terms satisfy condition

    private Map<Integer, Cycle<Set<GeneralizedRule>>> nrToScc; // and a mapping from the nr to the scc;
                                                    // here also singleton nodes with no edges are sccs!

    private IECap estimatedCap; // estimated cap algorithm
    private final IECap.CapFreshNameGenerator capFreshNames; // fresh name generator for estimatedCap

    // a graph where the nodes are the rules in P u R
    // and there is an edge from one rule to another
    // if whenever the first rule is usable, and the
    // conditions in the label are true, then the
    // other rule is also usable
    SimpleGraph<Set<GeneralizedRule>, IActiveCondition> depGraph;


    public IUsableRules(IDPRuleAnalysis ruleAnalysis, IECap estimatedCap) {
        this.ruleAnalysis = ruleAnalysis;
        this.estimatedCap = estimatedCap;
        this.capFreshNames = new IECap.CapFreshNameGenerator(ruleAnalysis.getRAnalysis().getVariables());
        FreshNameGenerator freshNames = new FreshNameGenerator(ruleAnalysis.getFunctionSymbols(), FreshNameGenerator.DEPENDENCY_PAIRS);
        this.unmatchable = FunctionSymbol.create(freshNames.getFreshName("unmatchable", false), 1);
    }

    private synchronized void init() {
        if (this.depGraph == null) {
            this.R = this.ruleAnalysis.getRAnalysis().getRuleMap();
            this.Q = this.ruleAnalysis.getQ();
            this.innermost = this.ruleAnalysis.isNfQSubsetEqNfR();

            // compute qrNormal conditions
            if (this.innermost) {
                Collection<TRSFunctionApplication> critQTerms = new LinkedHashSet<TRSFunctionApplication>(this.Q.getWrappedQ().getTerms());
                for (GeneralizedRule rule : this.ruleAnalysis.getRAnalysis().getRules()) {
                    critQTerms.remove(rule.getLhsInStandardRepresentation());
                }

                if (critQTerms.isEmpty()) {
                    this.criticalTermsInQ = null; // if Q \ lhs(R) is empty, we are trivially qrNormal, as in termination case
                } else {
                    this.criticalTermsInQ = new LinkedHashMap<FunctionSymbol, Collection<TRSFunctionApplication>>();
                    this.nodeToQRNormal = new LinkedHashMap<Node<Set<GeneralizedRule>>, Boolean>(this.ruleAnalysis.getRAnalysis().getRules().size());
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
            this.ruleMap = new LinkedHashMap<GeneralizedRule, Node<Set<GeneralizedRule>>>();
            Set<Node<Set<GeneralizedRule>>> nodes = new LinkedHashSet<Node<Set<GeneralizedRule>>>();

            this.addInitialNodes(this.ruleAnalysis.getRAnalysis().getRules(), nodes);
            for (FunctionSymbol f : this.ruleAnalysis.getFunctionSymbols()) {
                PredefinedFunction pf = this.ruleAnalysis.getPreDefinedMap().getPredefinedFunction(f);
                if (pf != null) {
                    if (pf.hasFiniteRuleSet()) {
                        this.addInitialNodes(pf.getFiniteRuleSet(f), nodes);
                    } else {
                        this.addInitialNode(pf.getAbstractRule(f), nodes);
                    }
                }
            }

            this.depGraph = new SimpleGraph<Set<GeneralizedRule>, IActiveCondition>(nodes);

            // add predefined Symbols

            // now compute all (non-recursive) usable rules and q
            for (Node<Set<GeneralizedRule>> node : nodes) {
                Boolean qrNormal = this.criticalTermsInQ != null; // if we trivially satisfy the check, then do no check
                GeneralizedRule rule = node.getObject().iterator().next().getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
                Set<TRSTerm> S = new LinkedHashSet<TRSTerm>(rule.getLeft().getArguments());
                S.addAll(rule.getUnboundedVariables());
                qrNormal = this.addInitialEdges(node, S, rule.getRight(), IActiveCondition.TRUE, qrNormal);
                // okay, in the trivial case set the proper value
                if (this.criticalTermsInQ != null) {
                    // store qrNormalValue
                    this.nodeToQRNormal.put(node, qrNormal);
                }
            }

            // merge nodes that are combined
            for (Cycle<Set<GeneralizedRule>> scc : this.depGraph.getSCCs(IUsableRules.TRUE_FILTER)) {
                this.mergeRuleNodes(scc);
            }

            // compute sccs and make lookup map for node->#scc and #scc -> scc
            // moreover, propagate qrNormal values
            Integer n = 0;
            this.nrToScc = new LinkedHashMap<Integer, Cycle<Set<GeneralizedRule>>>();
            this.nodeToSccNr = new LinkedHashMap<Node<Set<GeneralizedRule>>, Integer>(this.R.size());
            for (Cycle<Set<GeneralizedRule>> scc : this.depGraph.getSCCs(false)) {
               this.nrToScc.put(n, scc);
               if (this.nodeToQRNormal == null) {
                   // no propagation of qr-Normal values here
                   for (Node<Set<GeneralizedRule>> node : scc) {
                       this.nodeToSccNr.put(node, n);
                   }
               } else {
                   boolean qrNormal = true;
                   for (Node<Set<GeneralizedRule>> node : scc) {
                       this.nodeToSccNr.put(node, n);
                       if (qrNormal) {
                           qrNormal = this.nodeToQRNormal.get(node).booleanValue();
                       }
                   }

                   if (!qrNormal) {
                       for (Node<Set<GeneralizedRule>> node : scc) {
                           for (Node<Set<GeneralizedRule>> pred : this.depGraph.getIn(node)) {
                               this.nodeToQRNormal.put(pred, Boolean.FALSE);
                           }
                       }
                   }

               }

               n++;
            }

            // create lookup maps for dps
            this.dpMap = new LinkedHashMap<GeneralizedRule, Pair<GeneralizedRule,Node<Set<GeneralizedRule>>>>();
        }
    }

    private void addInitialNodes(Set<? extends GeneralizedRule> rules, Set<Node<Set<GeneralizedRule>>> nodes) {
        for (GeneralizedRule rule : rules) {
            this.addInitialNode(rule, nodes);
        }
    }

    private void addInitialNode(GeneralizedRule rule, Set<Node<Set<GeneralizedRule>>> nodes) {
        // System.err.println("Add initial node: " + rule + " -to-> " + nodes);
        Set<GeneralizedRule> ruleSet = new LinkedHashSet<GeneralizedRule>(1);
        ruleSet.add(rule);
        Node<Set<GeneralizedRule>> node = new Node<Set<GeneralizedRule>>(ruleSet);
        nodes.add(node);
        this.ruleMap.put(rule, node);
    }

    private void mergeRuleNodes(Set<Node<Set<GeneralizedRule>>> toMerge) {
        Node<Set<GeneralizedRule>> collapsed = this.depGraph.merge(toMerge, IUsableRules.NODE_UNION_COMBINER, IUsableRules.LABEL_OR_COMBINER);
        final boolean nonTrivial = this.criticalTermsInQ != null;
        boolean qrNormal = nonTrivial;
        for (Node<Set<GeneralizedRule>> node : toMerge) {
            for (GeneralizedRule rule : node.getObject()) {
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
    public Map<GeneralizedRule, IActiveCondition> getSpecializedActiveConditions(Map<GeneralizedRule, IActiveCondition> rules, IActiveCondition.IExtendedAfs afs) {
        Map<IActiveCondition, IActiveCondition> newConditions = new LinkedHashMap<IActiveCondition, IActiveCondition>();
        boolean changed = false;
        Iterator<Map.Entry<GeneralizedRule, IActiveCondition>> rulesIt = rules.entrySet().iterator();
        while (rulesIt.hasNext()) {
            Map.Entry<GeneralizedRule, IActiveCondition> rule = rulesIt.next();
            IActiveCondition cond = rule.getValue();
            IActiveCondition newCond = newConditions.get(cond);
            if (newCond == null) {
                // we have to compute the new condition
                newCond = cond.specialize(afs);
                newConditions.put(cond, newCond);
                // okay, we have to change something
                if (newCond != cond) {
                    // if this is the first change, create a new map
                    if (!changed) {
                        changed = true;
                        SortedMap<GeneralizedRule, IActiveCondition> newRules = new TreeMap<GeneralizedRule, IActiveCondition>(rules);
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
    public IdpQUsableRules getActiveConditions(Set<? extends GeneralizedRule> dps) {
        return this.getActiveConditions(dps, false);
    }

    /**
     * computes the active condition for the usable rules of a term.
     * @param dps
     * @return
     */
    @Override
    public IdpQUsableRules getActiveConditions(TRSTerm t) {
        this.init();
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(1);
        args.add(t);
        GeneralizedRule r = GeneralizedRule.create(TRSTerm.createFunctionApplication(this.unmatchable, ImmutableCreator.create(args)), t);
        this.addTerm(r);
        return this.getActiveConditions(Collections.singleton(r), false);
    }


    /**
     * computes the active condition for each T. This is done by labeling
     * the usable rules graph with boolean conditions and propogate these
     * values accordingly.
     * @param dps
     * @return
     */
    public IdpQUsableRules getTermActiveConditions(Set<TRSTerm> terms) {
        return null;
    }

    /**
     * computes the active condition for each DP. This is done by labeling
     * the usable rules graph with boolean conditions and propogate these
     * values accordingly.
     * @param dps
     * @param mergeMutual if true, then mutual recursive rules obtain one shared active condition
     * @return
     */
    public IdpQUsableRules getActiveConditions(Set<? extends GeneralizedRule> dps, boolean mergeMutual) {
        this.init();
        Set<Node<Set<GeneralizedRule>>> dpNodes = this.addDPs(dps);
        Set<Integer> todo = new TreeSet<Integer>(new Comparator<Integer>() {
            @Override
            public int compare(Integer arg0, Integer arg1) { return arg1.compareTo(arg0); }
        });  // traverse in reverse order to get high Sccs first!

        Map<Node<Set<GeneralizedRule>>, IActiveCondition> state = new LinkedHashMap<Node<Set<GeneralizedRule>>, IActiveCondition>(dps.size() + 10);

        // initially label every node reachable from DPs
        for (Node<Set<GeneralizedRule>> dpNode : dpNodes) {
            for (Edge<IActiveCondition, Set<GeneralizedRule>> edge :  this.depGraph.getOutEdges(dpNode)) {
                Node<Set<GeneralizedRule>> successor = edge.getEndNode();
                IActiveCondition succCond = state.get(successor);
                IActiveCondition edgeCond = edge.getObject();
                IActiveCondition newCond;
                if (succCond == null) {
                    newCond = edgeCond;
                } else {
                    if (!succCond.equals(IActiveCondition.TRUE)) {
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
            Cycle<Set<GeneralizedRule>> scc = this.nrToScc.get(nr);
            int n = scc.size();
            if (mergeMutual || n == 1) {
                IActiveCondition cond = null;
                for (Node<Set<GeneralizedRule>> node : scc) {
                    IActiveCondition curr = state.get(node);
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
                for (Node<Set<GeneralizedRule>> node : scc) {
                    state.put(node, cond);
                    for (Edge<IActiveCondition, Set<GeneralizedRule>> edge : this.depGraph.getOutEdges(node)) {
                        Node<Set<GeneralizedRule>> succ = edge.getEndNode();
                        Integer succNr = this.nodeToSccNr.get(succ);
                        // only look at edges out of current scc
                        if (!succNr.equals(nr)) {
                            todo.add(succNr);
                            IActiveCondition succCond = state.get(succ);
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
                Set<Node<Set<GeneralizedRule>>> toIterate = new LinkedHashSet<Node<Set<GeneralizedRule>>>(n);
                Set<Node<Set<GeneralizedRule>>> nextToIterate = new LinkedHashSet<Node<Set<GeneralizedRule>>>(n);

                // in the first round we do not have to propagate null values
                for (Node<Set<GeneralizedRule>> node : scc) {
                    if (state.get(node) != null) {
                        toIterate.add(node);
                    }
                }

                for (int i=0; i<n; i++) {

                    for (Node<Set<GeneralizedRule>> node : toIterate) {
                        IActiveCondition cond = state.get(node);
                        for (Edge<IActiveCondition, Set<GeneralizedRule>> edge : this.depGraph.getOutEdges(node)) {
                            Node<Set<GeneralizedRule>> succ = edge.getEndNode();
                            Integer succNr = this.nodeToSccNr.get(succ);
                            // only look at edges in the current scc
                            if (succNr.equals(nr)) {
                                IActiveCondition succCond = state.get(succ);
                                if (succCond == null) {
                                    state.put(succ, cond.and(edge.getObject()));
                                    nextToIterate.add(succ);
                                } else {
                                    IActiveCondition newCond = succCond.or(cond.and(edge.getObject()));
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
                    Set<Node<Set<GeneralizedRule>>> tmp = toIterate;
                    toIterate = nextToIterate;
                    nextToIterate = tmp;
                    nextToIterate.clear();
                }

                // at this point all information is passed inside the scc
                // now we have to propagate this values downwards
                for (Node<Set<GeneralizedRule>> node : scc) {
                    IActiveCondition cond = state.get(node);
                    for (Edge<IActiveCondition, Set<GeneralizedRule>> edge : this.depGraph.getOutEdges(node)) {
                        Node<Set<GeneralizedRule>> succ = edge.getEndNode();
                        Integer succNr = this.nodeToSccNr.get(succ);
                        // only look at edges out of current scc
                        if (!succNr.equals(nr)) {
                            todo.add(succNr);
                            IActiveCondition succCond = state.get(succ);
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
        Map<GeneralizedRule, IActiveCondition> result = new LinkedHashMap<GeneralizedRule, IActiveCondition>();
        for (Map.Entry<Node<Set<GeneralizedRule>>, IActiveCondition> entry : state.entrySet()) {
            IActiveCondition condition = entry.getValue();
            for (GeneralizedRule rule : entry.getKey().getObject()) {
                result.put(rule, condition);
            }
        }
        return IdpQUsableRules.create(ImmutableCreator.create(result));
    }

    /**
     * computes the usable rules for a given DP and
     * the underlying IDPRuleAnalysis (which was passed in the constructor)
     * @param dp
     * @return the set of usable rules, this set may be modified.
     */
    public Set<GeneralizedRule> getUsableRules(GeneralizedRule dp) {
        ArrayList<GeneralizedRule> theDp = new ArrayList<GeneralizedRule>(1);
        theDp.add(dp);
        return this.getUsableRules(theDp);
    }

    /**
     * computes whether there is at least one usable rule for a given DP and
     * the underlying IDPRuleAnalysis (which was passed in the constructor)
     * @param dp
     * @return true iff the usable rules for this dp are non-empty
     */
    public boolean hasUsableRules(GeneralizedRule dp) {
        this.init();
        Node<Set<GeneralizedRule>> node = this.addDP(dp).y;
        return !this.depGraph.getOut(node).isEmpty();
    }


    /**
     * computes the usable rules for a given set of DPs and
     * the underlying IDPRuleAnalysis (which was passed in the constructor)
     * @param dps
     * @return the set of usable rules, this set may be modified.
     */
    @Override
    public Set<GeneralizedRule> getUsableRules(Collection<GeneralizedRule> dps) {
        return this.getUsableRules(dps, null);
    }



    /**
     * computes the usable rules for a given set of DPs, a corresponding Afs,
     * and the underlying IDPRuleAnalysis (which was passed in the constructor)
     * @param dps
     * @param afs
     * @return the set of usable rules, this set may be modified.
     */
    public Set<GeneralizedRule> getUsableRules(Collection<GeneralizedRule> dps, final IActiveCondition.IExtendedAfs afs) {
        this.init();
        Set<Node<Set<GeneralizedRule>>> nodesForDPs = this.addDPs(dps);
        Set<Node<Set<GeneralizedRule>>> reachable;
        if (afs == null) {
            reachable = this.depGraph.determineReachableNodes(nodesForDPs);
        } else {
            EdgeFilter<IActiveCondition,Set<GeneralizedRule>> filter = new EdgeFilter<IActiveCondition, Set<GeneralizedRule>>() {
                @Override
                public boolean selectEdge(Node<Set<GeneralizedRule>> source, Node<Set<GeneralizedRule>> dest, IActiveCondition label) {
                    return label.specialize(afs).isSatisfiable();
                }
            };
            reachable = this.depGraph.determineReachableNodes(nodesForDPs, filter);
        }
        Set<GeneralizedRule> usable = new LinkedHashSet<GeneralizedRule>();
        for (Node<Set<GeneralizedRule>> node : reachable) {
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
    public boolean getQRNormal(GeneralizedRule dp) {
        this.init();
        if (this.nodeToQRNormal == null) {
            return true;
        } else {
            Node<Set<GeneralizedRule>> n = this.addDP(dp).y;
            return this.nodeToQRNormal.get(n).booleanValue();
        }
    }

    /**
     * computes whether all dps satisfy the qr-Normal condition
     * @param dps
     */
    public boolean getQRNormal(Iterable<? extends Rule> dps) {
        this.init();
        if (this.nodeToQRNormal == null) {
            return true;
        } else {
            for (GeneralizedRule dp : dps) {
                Node<Set<GeneralizedRule>> n = this.addDP(dp).y;
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
    public static Map<GeneralizedRule, IActiveCondition> getRulesAsConditionMap(Collection<GeneralizedRule> rules) {
        Map<GeneralizedRule, IActiveCondition> result = new LinkedHashMap<GeneralizedRule, IActiveCondition>(rules.size());
        for (GeneralizedRule rule : rules) {
            result.put(rule, IActiveCondition.TRUE);
        }
        return result;
    }

    /**
     * adds the dps to the graph and
     * returns the corresponding set of nodes
     * @param dps
     * @return the set of nodes for the DPs, the set may be modified
     */
    private Set<Node<Set<GeneralizedRule>>> addDPs(Collection<? extends GeneralizedRule> dps) {
        Set<Node<Set<GeneralizedRule>>> res = new LinkedHashSet<Node<Set<GeneralizedRule>>>(dps.size());
        for (GeneralizedRule dp : dps) {
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
    private synchronized Pair<GeneralizedRule,Node<Set<GeneralizedRule>>> addTerm(GeneralizedRule unmatchableRule) {

        Pair<GeneralizedRule, Node<Set<GeneralizedRule>>> cap_and_node = this.dpMap.get(unmatchableRule);
        if (cap_and_node == null) {
            Set<GeneralizedRule> dpLabel = new LinkedHashSet<GeneralizedRule>(1);
            dpLabel.add(unmatchableRule);
            Node<Set<GeneralizedRule>> n = new Node<Set<GeneralizedRule>>(dpLabel);
            this.depGraph.addNode(n);
            unmatchableRule = unmatchableRule.getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
            boolean calcQRNormal = this.criticalTermsInQ != null;
            Pair<TRSTerm, Boolean> cap_t_and_qrNormal = this.addDPEdges(n, null, unmatchableRule.getRight(), IActiveCondition.TRUE, calcQRNormal, true);
            if (calcQRNormal) {
                this.nodeToQRNormal.put(n, cap_t_and_qrNormal.y);
            }
            cap_and_node = new Pair<GeneralizedRule, Node<Set<GeneralizedRule>>>(GeneralizedRule.create(unmatchableRule.getLeft(), cap_t_and_qrNormal.x), n);
            this.dpMap.put(unmatchableRule, cap_and_node);
        }
        return cap_and_node;
    }

    /**
     * adds a dp to this calculator if not already added,
     * asserts that init() has been called before.
     * @param dp
     * @return the capped dp and the corresponding node
     */
    private synchronized Pair<GeneralizedRule,Node<Set<GeneralizedRule>>> addDP(GeneralizedRule dp) {
        Pair<GeneralizedRule, Node<Set<GeneralizedRule>>> cap_and_node = this.dpMap.get(dp);
        if (cap_and_node == null) {
            Set<GeneralizedRule> dpLabel = new LinkedHashSet<GeneralizedRule>(1);
            dpLabel.add(dp);
            Node<Set<GeneralizedRule>> n = new Node<Set<GeneralizedRule>>(dpLabel);
            this.depGraph.addNode(n);
            dp = dp.getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
            boolean calcQRNormal = this.criticalTermsInQ != null;
            Set<TRSTerm> S = new LinkedHashSet<TRSTerm>();
            S.add(dp.getLeft());
            S.addAll(dp.getUnboundedVariables());
            Pair<TRSTerm, Boolean> cap_t_and_qrNormal = this.addDPEdges(n, S, dp.getRight(), IActiveCondition.TRUE, calcQRNormal, this.innermost || !this.Q.canBeRewritten(dp.getLeft()));
            if (calcQRNormal) {
                this.nodeToQRNormal.put(n, cap_t_and_qrNormal.y);
            }
            cap_and_node = new Pair<GeneralizedRule, Node<Set<GeneralizedRule>>>(GeneralizedRule.create(dp.getLeft(), cap_t_and_qrNormal.x), n);
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
    public GeneralizedRule getCappedDP(GeneralizedRule dp) {
        this.init();
        return this.addDP(dp).x;
    }


    @Override
    public String toString() {
        this.init();
        StringBuffer t = new StringBuffer("digraph dp_graph {\nnode [outthreshold=100, inthreshold=100];\n");
        for (Node<Set<GeneralizedRule>> node : this.depGraph.getNodes()) {
            t.append(node.getNodeNumber()+" [");
            t.append("label=\"");
            boolean first = true;
            for (GeneralizedRule rule : node.getObject()) {
                if (first) {
                    first = false;
                } else {
                    t.append("\\n");
                }
                t.append(rule.toString());
            }
            t.append("\", fontsize=16];\n");
        }
        for (Edge<IActiveCondition, Set<GeneralizedRule>> edge : this.depGraph.getEdges()) {
            t.append(edge.getStartNode().getNodeNumber() + " -> "
                    + edge.getEndNode().getNodeNumber());
            t.append("[label=\"" + edge.getObject() + "\"];\n");
        }
        t.append("}\n");
        return t.toString();
    }

    /**
     * @param fromNode
     * @param s a set of terms used with @see{IECap}
     * @param r a (part of) rhs of a rule (l -> C[r]), with variables of THIRD_STANDARD_PREFIX
     * @param cond
     * @param qrNormal - have we a chance to satisfy qrNormal up to now?
     * @return true iff the input qrNormal is true and for the term r we
     *         have that every r does not conflict with the qr-implies-q-normal condition directly! (without tracking usable rules)
     */
    private Boolean addInitialEdges(Node<Set<GeneralizedRule>> fromNode, Set<? extends TRSTerm> s, TRSTerm r, IActiveCondition cond, Boolean qrNormal) {
        Pair<TRSTerm, ImmutableMap<Position,ImmutableSet<GeneralizedRule>>> capped = this.estimatedCap.cap(this.ruleAnalysis, s, r, this.capFreshNames, true, true);
        // System.err.println("AddInitial Edge: " + fromNode + " ---> " + r);
        for (Map.Entry<Position,ImmutableSet<GeneralizedRule>> p : capped.y.entrySet()) {
            Position suffix = p.getKey();
            TRSTerm t = r;
            IActiveCondition c = cond;
            // System.err.println("addEdges: " + t + " -> "+  suffix);
            if (suffix.getDepth() > 0) {
                for (Integer i : suffix) {
                    TRSFunctionApplication fa = ((TRSFunctionApplication) t);
                    c = c.and(fa.getRootSymbol(), i);
                    t = fa.getArgument(i);
                    if (qrNormal.booleanValue()) {
                        Collection<TRSFunctionApplication> critTerms = this.criticalTermsInQ.get(fa.getRootSymbol());
                        if (critTerms != null) {
                            for (TRSFunctionApplication critTerm : critTerms) {
                                if (critTerm.unifies(fa)) {
                                    qrNormal = Boolean.FALSE;
                                }
                            }
                        }
                    }
                }
            }
            if (!t.isVariable()) {
                for (GeneralizedRule rule : p.getValue()) {
                    this.addEdge(fromNode, this.ruleMap.get(rule), c);
                }
                TRSFunctionApplication fa = ((TRSFunctionApplication)t);
                FunctionSymbol root = fa.getRootSymbol();
                for (int i = root.getArity()-1; i>=0; i--) {
                    qrNormal = this.addInitialEdges(fromNode, s, fa.getArgument(i), c.and(root, i), qrNormal);
                }
            }
        }
        return qrNormal;
    }

    /**
     * the method is very similar to <code>addInitialEdges</code>
     * @param fromNode draw edges from this node
     * @param s consider this term as lhs
     * @param t a subterm of the original rhs
     * @param cond the condition so far
     * @param qrNormal chance to satisfy qrNormal
     * @param sInQNF is s a Q-normal form or not (in innermost case this value may always be true, as a harder check is performed in this routine)
     * @return (cap_s(t), qrNormal can be satisfied) where vars in cap_s(t) are from 2. and 3. prefix
     */
    private Pair<TRSTerm, Boolean> addDPEdges(Node<Set<GeneralizedRule>> fromNode, Set<TRSTerm> s, TRSTerm term, IActiveCondition cond, Boolean qrNormal, final boolean sInQNF) {
        // System.err.println("addDPEdges: " + fromNode + " <======> " + term);
        Pair<TRSTerm, ImmutableMap<Position,ImmutableSet<GeneralizedRule>>> capped = this.estimatedCap.cap(this.ruleAnalysis, s != null ? s : Collections.<TRSTerm>emptySet(), term, this.capFreshNames, true, true);
        for (Map.Entry<Position,ImmutableSet<GeneralizedRule>> p : capped.y.entrySet()) {
            // System.err.println("addEdges: " + term + " -> "+ p.getKey());
            Position suffix = p.getKey();
            TRSTerm t = term;
            IActiveCondition c = cond;
            // System.err.println("addEdges: " + currentTerm + " @ " + currentPos + " -> "+ p.getPosition() + " = " + suffix);
            if (suffix.getDepth() > 0) {
                for (Integer i : suffix) {
                    TRSFunctionApplication fa = ((TRSFunctionApplication) t);
                    c = c.and(fa.getRootSymbol(), i);
                    t = fa.getArgument(i);
                    // and update qrNormal value for this term
                    // update qr-normal value from rules
                    if (qrNormal.booleanValue()) {
                        Collection<TRSFunctionApplication> critTerms = this.criticalTermsInQ.get(fa.getRootSymbol());
                        if (critTerms != null) {
                            for (TRSFunctionApplication critTerm : critTerms) {
                                if (critTerm.unifies(fa)) {
                                    qrNormal = Boolean.FALSE;
                                }
                            }
                        }
                    }
                }
            }
            if (!t.isVariable()) {
                for (GeneralizedRule rule : p.getValue()) {
                    // FunctionSymbol root = rule.getLeft().getRootSymbol();
                    //if (!PredefinedFunctions.isPredefined(root) || PredefinedFunctions.getFunction(root).hasFiniteRuleSet()) {
                        this.addEdge(fromNode, this.ruleMap.get(rule), c);
                    //}
                }
                TRSFunctionApplication fa = ((TRSFunctionApplication)t);
                FunctionSymbol root = fa.getRootSymbol();
                for (int i = root.getArity()-1; i>=0; i--) {
                    qrNormal = this.addDPEdges(fromNode, s, fa.getArgument(i), c.and(root, i), qrNormal, sInQNF).y;
                }
            }
        }
        return new Pair<TRSTerm, Boolean>(capped.x, qrNormal);
    }


    private void addEdge(Node<Set<GeneralizedRule>> from, Node<Set<GeneralizedRule>> to, IActiveCondition cond) {
        if (from != to && to != null) {
            // System.err.println("addEdge: " + from + " --->>> " + to + " IFF " + cond);
            this.depGraph.mergeEdge(from, to, cond, IUsableRules.LABEL_OR_COMBINER);
        }
    }


    private static final BinaryOperation<Set<GeneralizedRule>> NODE_UNION_COMBINER = new BinaryOperation<Set<GeneralizedRule>>() {
        @Override
        public Set<GeneralizedRule> combine(Set<GeneralizedRule> one, Set<GeneralizedRule> two) {
            one.addAll(two);
            return one;
        }
    };


    private final static EdgeFilter<IActiveCondition, Set<GeneralizedRule>> TRUE_FILTER = new EdgeFilter<IActiveCondition, Set<GeneralizedRule>>() {
        @Override
        public boolean selectEdge(Node<Set<GeneralizedRule>> from, Node<Set<GeneralizedRule>> to, IActiveCondition label) {
            return label == IActiveCondition.TRUE;
        }
    };


    private static final BinaryOperation<IActiveCondition> LABEL_OR_COMBINER = new BinaryOperation<IActiveCondition>() {
        @Override
        public IActiveCondition combine(IActiveCondition one, IActiveCondition two) {
            return one.or(two);
        }
    };

    @Override
    public IdpQUsableRules getUsableRules(IDPRuleAnalysis ruleAnalysis) {
        return this.getActiveConditions(ruleAnalysis.getPAnalysis().getRules());
    }

}
