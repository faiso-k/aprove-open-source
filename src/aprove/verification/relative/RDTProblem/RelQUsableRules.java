package aprove.verification.relative.RDTProblem;

import java.util.*;

import aprove.*;
import aprove.runtime.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * based on @see aprove.verification.relative.PDPProblem.ProbQUsableRules
 * 
 * @author Grigory Vartanyan
 * @version $Id$
 */
public class RelQUsableRules {

    // ================================================================================
    // Properties
    // ================================================================================

    private final QTRSProblem qtrs;
    private boolean innermost;

    // a mapping from rules to their nodes
    private Map<RuleSchema, Node<Set<RuleSchema>>> ruleMap;
    // a mapping from function symbols to corresponding rules, repr. R
    private Map<FunctionSymbol, ? extends Set<Rule>> R;
    // a mapping from function symbols to lhss of Q \ lhs(R), if innermost and non-empty set. All with standard prefix vars.
    private Map<FunctionSymbol, Collection<TRSFunctionApplication>> criticalTermsInQ;

    private QTermSet Q;
    // dp to capped dp (in third standard) and corresponding node
    private Map<CoupledPosDepTuple, Pair<CappedCoupledPosDepTuple, Node<Set<RuleSchema>>>> dpMap;

    // a mapping from dps to capped lhss wrt. to R^-1, only in termination case and only if R^-1 is non-collapsing
    private Map<CoupledPosDepTuple, TRSTerm> dpToCappedRminusOneU;
    // a mapping from dps to their usable rules ^-1, only in innermost case
    private Map<CoupledPosDepTuple, Map<FunctionSymbol, Set<Rule>>> dpToUsedRminusOneST;

    // a mapping from nodes to a scc-nr
    private Map<Node<Set<RuleSchema>>, Integer> nodeToSccNr;
    // a mapping from nodes to qr-normal conditions; null, iff criticalTermsInQ is null iff all terms satisfy condition
    private Map<Node<Set<RuleSchema>>, Boolean> nodeToQRNormal;

    // and a mapping from the nr to the scc; here also singleton nodes with no edges are sccs!
    private Map<Integer, Cycle<Set<RuleSchema>>> nrToScc;

    // a graph where the nodes are the rules in P u R and there is an edge from one rule to another
    // if whenever the first rule is usable, and the conditions in the label are true, then the other rule is also usable
    SimpleGraph<Set<RuleSchema>, QActiveCondition> depGraph;

    private final static TRSVariable Y = TRSVariable.createVariable(TRSTerm.SECOND_STANDARD_PREFIX);

    // ================================================================================
    // Constructors and Creators
    // ====================================================s============================

    public RelQUsableRules(QTRSProblem qtrs) {
        this.qtrs = qtrs;
        this.init();
    }

    // ================================================================================
    // Accessors
    // ================================================================================

    public QTRSProblem getUnderlyingQTRS() {
        return this.qtrs;
    }

    /**
     * computes whether there is at least one usable rule for a given DP and the
     * underlying QTRS (which was passed in the constructor)
     * 
     * @param dp
     * @return true iff the usable rules for this dp are non-empty
     */
    public boolean hasUsableRules(CoupledPosDepTuple dp) {
        // init();
        Node<Set<RuleSchema>> node = this.addDP(dp).y;
        return !this.depGraph.getOut(node).isEmpty();
    }

    /**
     * computes the usable rules for a given DP and the underlying QTRS (which was
     * passed in the constructor)
     * 
     * @param dp
     * @return the set of usable rules, this set may be modified.
     */
    public Set<Rule> getUsableRules(CoupledPosDepTuple dp) {
        ArrayList<CoupledPosDepTuple> theDp = new ArrayList<CoupledPosDepTuple>(1);
        theDp.add(dp);
        return this.getUsableRules(theDp);
    }

    /**
     * computes the usable rules for a given set of DPs and the underlying QTRS
     * (which was passed in the constructor)
     * 
     * @param dps
     * @return the set of usable rules, this set may be modified.
     */
    public Set<Rule> getUsableRules(Collection<CoupledPosDepTuple> dps) {
        return this.getUsableRules(dps, null);
    }

    /**
     * computes the usable rules for a given set of DPs, a corresponding Afs, and
     * the underlying QTRS (which was passed in the constructor)
     * 
     * @param dps
     * @param afs
     * @return the set of usable rules, this set may be modified.
     */
    public Set<Rule> getUsableRules(Collection<CoupledPosDepTuple> dps,
            final QActiveCondition.Afs afs) {
        // init();
        Set<Node<Set<RuleSchema>>> nodesForDPs = this.addDPs(dps);
        Set<Node<Set<RuleSchema>>> reachable;
        if (afs == null) {
            reachable = this.depGraph.determineReachableNodes(nodesForDPs);
        } else {
            EdgeFilter<QActiveCondition, Set<RuleSchema>> filter = new EdgeFilter<QActiveCondition, Set<RuleSchema>>() {

                @Override
                public boolean selectEdge(Node<Set<RuleSchema>> source, Node<Set<RuleSchema>> dest,
                        QActiveCondition label) {
                    return label.specialize(afs).isSatisfiable();
                }
            };
            reachable = this.depGraph.determineReachableNodes(nodesForDPs, filter);
        }
        Set<Rule> usable = new LinkedHashSet<Rule>();
        for (Node<Set<RuleSchema>> node : reachable) {
            // add rules only of rule nodes!
            if (!nodesForDPs.contains(node)) {
                for (RuleSchema ruleSchema : node.getObject()) {
                    Rule probRule = (Rule) ruleSchema;
                    usable.add(probRule);
                }
            }
        }

        return usable;
    }

    /**
     * computes whether the dp satisfies the qr-Normal condition
     * 
     * @param dp
     */
    public boolean getQRNormal(CoupledPosDepTuple dp) {
        // init();
        if (this.nodeToQRNormal == null) {
            return true;
        } else {
            Node<Set<RuleSchema>> n = this.addDP(dp).y;
            return this.nodeToQRNormal.get(n).booleanValue();
        }
    }

    /**
     * computes whether all dps satisfy the qr-Normal condition
     * 
     * @param dps
     */
    public boolean getQRNormal(Iterable<? extends CoupledPosDepTuple> dps) {
        if (this.nodeToQRNormal == null) {
            return true;
        } else {
            for (CoupledPosDepTuple dp : dps) {
                Node<Set<RuleSchema>> n = this.addDP(dp).y;
                boolean res = this.nodeToQRNormal.get(n).booleanValue();
                if (!res) {
                    return false;
                }
            }
            return true;
        }
    }

    /**
     * returns the capped dp (where variables are only from 2. and 3. standard
     * prefix) Capping was done by renaming the dp to 3. prefix and introducing 2.
     * prefix
     * 
     * @param dp
     * @return
     */
    public CappedCoupledPosDepTuple getCappedDP(CoupledPosDepTuple dp) {
        return this.addDP(dp).x;
    }

    /**
     * computes cap_R^-1(u) (where vars are from 2. prefix). Note that this method
     * may only be called in termination case.
     * 
     * @param u_to_v a dp
     */
    public synchronized TRSTerm getCapRminusOneOfU(CoupledPosDepTuple u_to_v) {
        if (this.dpToCappedRminusOneU == null) {
            return RelQUsableRules.Y;
        } else {
            TRSTerm capped = this.dpToCappedRminusOneU.get(u_to_v);
            if (capped == null) {
                capped = RelQUsableRules.computeCapRminusOne(u_to_v.getTupleLeft(), 0, this.qtrs.getReverseRuleMap()).x;
                this.dpToCappedRminusOneU.put(u_to_v, capped);
            }
            return capped;
        }
    }

    /**
     * computes cap_U(s_to_t,R) (u) (where vars are from 2. prefix). This method may
     * only be called in the innermost case.
     * 
     * @param s_to_t
     * @param u_to_v
     * @return
     */
    public TRSTerm getCapUsedRminusOneOfU(CoupledPosDepTuple s_to_t, CoupledPosDepTuple u_to_v) {
        Map<FunctionSymbol, Set<Rule>> usableRules;
        synchronized (this) {
            usableRules = this.dpToUsedRminusOneST.get(s_to_t);
            if (usableRules == null) {
                usableRules = Rule.getReversedRuleMap(this.getUsableRules(s_to_t));
                this.dpToUsedRminusOneST.put(s_to_t, usableRules);
            }
        }

        if (usableRules.get(null) != null) { // we have a collapsing usable rule
            return RelQUsableRules.Y;
        } else {
            return RelQUsableRules.computeCapRminusOne(u_to_v.getTupleLeft(), 0, usableRules).x;
        }
    }

    // ================================================================================
    // Internals
    // ================================================================================

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
                    this.criticalTermsInQ = null; // if Q \ lhs(R) is empty, we are trivially qrNormal, as in
                                                 // termination case
                } else {
                    this.criticalTermsInQ = new HashMap<FunctionSymbol, Collection<TRSFunctionApplication>>();
                    this.nodeToQRNormal = new HashMap<Node<Set<RuleSchema>>, Boolean>(this.qtrs.getR().size());
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
                // in termination case Q supset lhs(R) is not satisfied, hence qrNormal is
                // trivially satisfied
                this.criticalTermsInQ = null;
            }

            // now construct the graph
            this.ruleMap = new LinkedHashMap<RuleSchema, Node<Set<RuleSchema>>>();
            Set<Node<Set<RuleSchema>>> nodes = new LinkedHashSet<Node<Set<RuleSchema>>>();
            for (Rule rule : this.qtrs.getR()) {
                Set<RuleSchema> ruleSet = new LinkedHashSet<RuleSchema>(1);
                ruleSet.add(rule);
                Node<Set<RuleSchema>> node = new Node<Set<RuleSchema>>(ruleSet);
                nodes.add(node);
                this.ruleMap.put(rule, node);
            }

            this.depGraph = new SimpleGraph<Set<RuleSchema>, QActiveCondition>(nodes);

            // now compute all (non-recursive) usable rules and q
            for (Node<Set<RuleSchema>> node : nodes) {
                Boolean qrNormal = this.criticalTermsInQ != null; // if we trivially satisfy the check, then do no check
                RuleSchema ruleSchema = node.getObject().iterator().next();
                Rule probRule = ((Rule) ruleSchema)
                        .getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
                    TRSTerm term = probRule.getRight();

                    // TODO: What is qrNormal?
                    qrNormal = this.addInitialEdges(node, probRule.getLeft(), term, 0, QActiveCondition.TRUE,
                            qrNormal).z;
//                }
                // okay, in the trivial case set the proper value
                if (this.criticalTermsInQ != null) {
                    // store qrNormalValue
                    this.nodeToQRNormal.put(node, qrNormal);
                }
            }

            // merge nodes that are combined
            for (Cycle<Set<RuleSchema>> scc : this.depGraph.getSCCs(RelQUsableRules.TRUE_FILTER)) {
                this.mergeRuleNodes(scc);
            }

            // compute sccs and make lookup map for node->#scc and #scc -> scc
            // moreover, propagate qrNormal values
            Integer n = 0;
            this.nrToScc = new HashMap<Integer, Cycle<Set<RuleSchema>>>();
            this.nodeToSccNr = new HashMap<Node<Set<RuleSchema>>, Integer>(this.R.size());
            for (Cycle<Set<RuleSchema>> scc : this.depGraph.getSCCs(false)) {
                this.nrToScc.put(n, scc);
                if (this.nodeToQRNormal == null) {
                    // no propagation of qr-Normal values here
                    for (Node<Set<RuleSchema>> node : scc) {
                        this.nodeToSccNr.put(node, n);
                    }
                } else {
                    boolean qrNormal = true;
                    for (Node<Set<RuleSchema>> node : scc) {
                        this.nodeToSccNr.put(node, n);
                        if (qrNormal) {
                            qrNormal = this.nodeToQRNormal.get(node).booleanValue();
                        }
                    }

                    if (!qrNormal) {
                        for (Node<Set<RuleSchema>> node : scc) {
                            for (Node<Set<RuleSchema>> pred : this.depGraph.getIn(node)) {
                                this.nodeToQRNormal.put(pred, Boolean.FALSE);
                            }
                        }
                    }

                }

                n++;
            }

            // create lookup maps for dps
            this.dpMap = new HashMap<CoupledPosDepTuple, Pair<CappedCoupledPosDepTuple, Node<Set<RuleSchema>>>>();
            if (this.innermost) {
                this.dpToUsedRminusOneST = new HashMap<CoupledPosDepTuple, Map<FunctionSymbol, Set<Rule>>>();
            } else {
                if (!this.qtrs.isCollapsing()) {
                    this.dpToCappedRminusOneU = new HashMap<CoupledPosDepTuple, TRSTerm>();
                }
            }

        }
    }

    private void mergeRuleNodes(Set<Node<Set<RuleSchema>>> toMerge) {
        Node<Set<RuleSchema>> collapsed = this.depGraph.merge(toMerge, RelQUsableRules.NODE_UNION_COMBINER,
                RelQUsableRules.LABEL_OR_COMBINER);
        final boolean nonTrivial = this.criticalTermsInQ != null;
        boolean qrNormal = nonTrivial;
        for (Node<Set<RuleSchema>> node : toMerge) {
            for (RuleSchema rule : node.getObject()) {
                this.ruleMap.put(rule, collapsed);
                if (qrNormal) {
                    qrNormal = this.nodeToQRNormal.get(node).booleanValue();
                }
            }
        }

        // store new qrNormal value if needed
        // (if qrNormal was true, then all nodes have true in the end, nothing to
        // change)
        if (nonTrivial && !qrNormal) {
            this.nodeToQRNormal.put(collapsed, Boolean.FALSE);
        }

        this.depGraph.removeEdge(collapsed, collapsed);
    }

    /**
     * adds the dps to the graph and returns the corresponding set of nodes
     * 
     * @param dps
     * @return the set of nodes for the DPs, the set may be modified
     */
    private Set<Node<Set<RuleSchema>>> addDPs(Collection<CoupledPosDepTuple> dps) {
        Set<Node<Set<RuleSchema>>> res = new LinkedHashSet<Node<Set<RuleSchema>>>(dps.size());
        for (CoupledPosDepTuple dp : dps) {
            res.add(this.addDP(dp).y);
        }
        return res;
    }

    /**
     * adds a dp to this calculator if not already added, asserts that init() has
     * been called before.
     * 
     * @param dp
     * @return the capped dp and the corresponding node
     */
    private synchronized Pair<CappedCoupledPosDepTuple, Node<Set<RuleSchema>>> addDP(CoupledPosDepTuple dp) {
        Pair<CappedCoupledPosDepTuple, Node<Set<RuleSchema>>> cap_and_node = this.dpMap.get(dp);
        if (cap_and_node == null) {
            Set<RuleSchema> dpLabel = new HashSet<RuleSchema>(1);
            dpLabel.add(dp);
            Node<Set<RuleSchema>> n = new Node<Set<RuleSchema>>(dpLabel);
            this.depGraph.addNode(n);
            dp = dp.getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
            boolean calcQRNormal = this.criticalTermsInQ != null;

            Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> CoupledTermSetTerm = dp.getRightPair();
            Set<Pair<TRSFunctionApplication, Position>> termSet = CoupledTermSetTerm.getKey();
            TRSTerm coupledTerm = CoupledTermSetTerm.getValue();

            HashSet<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>> cappedTermPosSet = new HashSet<>();

            for (Pair<TRSFunctionApplication, Position> termPosPair : termSet) {
                Triple<TRSTerm, Integer, Boolean> cap_t_and_qrNormal = this.addDPEdges(n, dp.getTupleLeft(),
                        termPosPair.x, 0, QActiveCondition.TRUE, calcQRNormal,
                        this.innermost || !this.Q.canBeRewritten(dp.getLeft()));
                if (calcQRNormal) {
                    this.nodeToQRNormal.put(n, cap_t_and_qrNormal.z);
                }
                cappedTermPosSet.add(new Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>(
                        new Pair<>((TRSFunctionApplication) cap_t_and_qrNormal.x, termPosPair.x), termPosPair.y));
            }
            Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> coupledCappedRHS = new Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, TRSTerm>(
                    cappedTermPosSet, coupledTerm);

            cap_and_node = new Pair<CappedCoupledPosDepTuple, Node<Set<RuleSchema>>>(
                    CappedCoupledPosDepTuple.create(dp.getLeftPair(), coupledCappedRHS), n);
            this.dpMap.put(dp, cap_and_node);
        }
        return cap_and_node;
    }

    /**
     * the method is very similar to <code>addInitialEdges</code>
     * 
     * @param fromNode draw edges from this node
     * @param s        consider this term as lhs
     * @param t        a subterm of the original rhs
     * @param nr       the number for the next free var
     * @param cond     the condition so far
     * @param qrNormal chance to satisfy qrNormal
     * @param sInQNF   is s a Q-normal form or not (in innermost case this value may
     *                 always be true, as a harder check is performed in this
     *                 routine)
     * @return (cap_s(t),next nr for free var, qrNormal can be satisfied) where vars
     *         in cap_s(t) are from 2. and 3. prefix
     */
    private Triple<TRSTerm, Integer, Boolean> addDPEdges(Node<Set<RuleSchema>> fromNode, TRSTerm s, TRSTerm t,
            Integer nr, QActiveCondition cond, Boolean qrNormal, final boolean sInQNF) {
        if (Globals.useAssertions) {
            assert (t.checkVariablePrefix(TRSTerm.THIRD_STANDARD_PREFIX));
            assert (s.checkVariablePrefix(TRSTerm.THIRD_STANDARD_PREFIX));
        }

        if (t.isVariable()) {
            if (this.innermost) {
                return new Triple<TRSTerm, Integer, Boolean>(t, nr, qrNormal);
            } else {
                return new Triple<TRSTerm, Integer, Boolean>(
                        TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX + "_" + nr), nr + 1, qrNormal);
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
                Triple<TRSTerm, Integer, Boolean> argRes = this.addDPEdges(fromNode, s, arg, nr, condArg, qrNormal,
                        sInQNF);
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
                for (RuleSchema rule : possibleRules) {
                    TRSFunctionApplication l = rule.getLhsInStandardRepresentation();
                    boolean drawEdge;
                    if (this.innermost && !Options.certifier.isA3pat() && !Options.certifier.isRainbow()) {
                        TRSSubstitution sigma = ft.getMGU(l);
                        if (sigma == null) {
                            drawEdge = false;
                        } else {
                            drawEdge = !this.Q.canBeRewritten(s.applySubstitution(sigma))
                                    && !this.Q.canBeRewrittenBelowRoot(l.applySubstitution(sigma));
                        }
                    } else {
                        drawEdge = Options.certifier.isA3pat() || Options.certifier.isRainbow() || ft.unifies(l); // a3pat
                                                                                                                 // and
                                                                                                                 // rainbow
                                                                                                                 // can
                                                                                                                 // only
                                                                                                                 // do
                                                                                                                 // EDG!
                    }
                    if (drawEdge) {
                        someConnection = true;
                        Node<Set<RuleSchema>> ruleNode = this.ruleMap.get(rule);
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
                return new Triple<TRSTerm, Integer, Boolean>(
                        TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX + "_" + nr), nr + 1, qrNormal);
            } else {
                return new Triple<TRSTerm, Integer, Boolean>(ft, nr, qrNormal);
            }
        }
    }

    /**
     * computes CapR^-1(t) where rMinusOne has to be non-Collapsing
     * 
     * @param t
     * @param nr
     * @param immutableMap
     * @return the capped term and the next free var, where the capped term has vars
     *         from 2. prefix only
     */
    private static Pair<TRSTerm, Integer> computeCapRminusOne(TRSTerm t, Integer nr,
            Map<FunctionSymbol, ? extends Set<Rule>> immutableMap) {
        if (Globals.useAssertions) {
            assert (immutableMap.get(null) == null);
        }

        if (t.isVariable()) {
            return new Pair<TRSTerm, Integer>(TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX + "_" + nr),
                    nr + 1);
        } else {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            FunctionSymbol f = ft.getRootSymbol();
            ImmutableList<? extends TRSTerm> args = ft.getArguments();
            List<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
            int i = 0;
            Integer oldNr = nr;
            for (TRSTerm arg : args) {
                Pair<TRSTerm, Integer> argRes = RelQUsableRules.computeCapRminusOne(arg, nr, immutableMap);
                newArgs.add(argRes.x);
                nr = argRes.y;
                i++;
            }
            if (!nr.equals(oldNr)) {
                ft = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(newArgs));
            }

            // now we have the term f(cap(t_1), ..., cap(t_n)) in ft
            // let us check whether some rule unifies at top position
            Set<Rule> possibleRules = immutableMap.get(f);
            if (possibleRules != null) {
                for (Rule rule : possibleRules) {
                    TRSTerm r = rule.getRhsInStandardRepresentation();
                    if (ft.unifies(r)) {
                        return new Pair<TRSTerm, Integer>(
                                TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX + "_" + nr), nr + 1);
                    }
                }
            }

            return new Pair<TRSTerm, Integer>(ft, nr);
        }
    }

    /**
     * @param fromNode
     * @param l        the lhs of a rule, with variables of THIRD_STANDARD_PREFIX
     * @param r        a (part of) rhs of a rule (l -> C[r]), with variables of
     *                 THIRD_STANDARD_PREFIX
     * @param nr       the next free variable to be chosen
     * @param cond
     * @param qrNormal - have we a chance to satisfy qrNormal up to now?
     * @return the triple (cap(r), new_nr, qrnormal) where new_nr is the next free
     *         variable one can create, and qrnormal is true iff the input qrNormal
     *         is true and for the term r we have that every r does not conflict
     *         with the qr-implies-q-normal condition directly! (without tracking
     *         usable rules) The vars of cap(r) are from 2. and 3. prefix
     */
    private Triple<TRSTerm, Integer, Boolean> addInitialEdges(Node<Set<RuleSchema>> fromNode, TRSTerm l, TRSTerm r,
            Integer nr, QActiveCondition cond, Boolean qrNormal) {
        if (Globals.useAssertions) {
            assert (l.checkVariablePrefix(TRSTerm.THIRD_STANDARD_PREFIX));
            assert (r.checkVariablePrefix(TRSTerm.THIRD_STANDARD_PREFIX));
        }
        if (r.isVariable()) {
            if (this.innermost) {
                return new Triple<TRSTerm, Integer, Boolean>(r, nr, qrNormal);
            } else {
                return new Triple<TRSTerm, Integer, Boolean>(
                        TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX + "_" + nr), nr + 1, qrNormal);
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
                Triple<TRSTerm, Integer, Boolean> argRes = this.addInitialEdges(fromNode, l, arg, nr, condArg,
                        qrNormal);
                newArgs.add(argRes.x);
                nr = argRes.y;
                qrNormal = argRes.z;
                i++;
            }
            if (!nr.equals(oldNr)) {
                fr = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(newArgs));
            }

            // now we have the term f(cap(r_1), ..., cap(r_n)) in fr (with second or third
            // standard prefix vars only)
            // let us check which rules can be connected at top position
            boolean someConnection = false;
            Set<Rule> possibleRules = this.R.get(f);
            if (possibleRules != null) {
                for (RuleSchema rule : possibleRules) {
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
                return new Triple<TRSTerm, Integer, Boolean>(
                        TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX + "_" + nr), nr + 1, qrNormal);
            } else {
                return new Triple<TRSTerm, Integer, Boolean>(fr, nr, qrNormal);
            }
        }
    }

    private void addEdge(Node<Set<RuleSchema>> from, Node<Set<RuleSchema>> to, QActiveCondition cond) {
        if (from != to) {
            this.depGraph.mergeEdge(from, to, cond, RelQUsableRules.LABEL_OR_COMBINER);
        }
    }

    private static final BinaryOperation<Set<RuleSchema>> NODE_UNION_COMBINER = new BinaryOperation<Set<RuleSchema>>() {

        @Override
        public Set<RuleSchema> combine(Set<RuleSchema> one, Set<RuleSchema> two) {
            one.addAll(two);
            return one;
        }
    };

    private final static EdgeFilter<QActiveCondition, Set<RuleSchema>> TRUE_FILTER = new EdgeFilter<QActiveCondition, Set<RuleSchema>>() {

        @Override
        public boolean selectEdge(Node<Set<RuleSchema>> from, Node<Set<RuleSchema>> to, QActiveCondition label) {
            return label == QActiveCondition.TRUE;
        }
    };

    private static final BinaryOperation<QActiveCondition> LABEL_OR_COMBINER = new BinaryOperation<QActiveCondition>() {

        @Override
        public QActiveCondition combine(QActiveCondition one, QActiveCondition two) {
            return one.or(two);
        }
    };

    // ================================================================================
    // Statics
    // ================================================================================

    /**
     * transforms a gives set of rules to pseudo active usable rules (where all
     * conditions are TRUE, so in fact there is no active)
     * 
     * @param rules
     * @return
     */
    public static Map<RuleSchema, QActiveCondition> getRulesAsConditionMap(Collection<RuleSchema> rules) {
        Map<RuleSchema, QActiveCondition> result = new LinkedHashMap<RuleSchema, QActiveCondition>(rules.size());
        for (RuleSchema rule : rules) {
            result.put(rule, QActiveCondition.TRUE);
        }
        return result;
    }

    // ================================================================================
    // Utility
    // ================================================================================

    @Override
    public String toString() {
        // init();
        StringBuffer t = new StringBuffer("digraph dp_graph {\nnode [outthreshold=100, inthreshold=100];\n");
        for (Node<Set<RuleSchema>> node : this.depGraph.getNodes()) {
            t.append(node.getNodeNumber() + " [");
            t.append("label=\"");
            boolean first = true;
            for (RuleSchema rule : node.getObject()) {
                if (first) {
                    first = false;
                } else {
                    t.append("\\n");
                }
                t.append(rule.toString());
            }
            t.append("\", fontsize=16];\n");
        }
        for (Edge<QActiveCondition, Set<RuleSchema>> edge : this.depGraph.getEdges()) {
            t.append(edge.getStartNode().getNodeNumber() + " -> " + edge.getEndNode().getNodeNumber());
            t.append("[label=\"" + edge.getObject() + "\"];\n");
        }
        t.append("}\n");
        return t.toString();
    }

}
