/*
 * Created on 11.04.2005
 */
package aprove.verification.dpframework.TRSProblem;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Output.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.Graph.Node;
import aprove.verification.oldframework.Utility.Profiling.*;
import aprove.verification.oldframework.Utility.Profiling.FeaturesQTRS.*;
import aprove.verification.relative.RDTProblem.*;
import aprove.xml.*;
import immutables.*;

public final class QTRSProblem extends DefaultBasicObligation
        implements HTML_Able, HasTRSTerms, ExternUsable, XMLObligationExportable,
        HasFeatureVector<FeaturesQTRS.Features> {

    private final ImmutableSet<Rule> R;
    private final QTermSet Q;

    // cached / calculated values
    private final int hashCode;
    private final boolean QsuperR;
    private volatile CriticalPairs critPairs;
    private Integer maxArity;
    private final ImmutableSet<FunctionSymbol> signature;        // signature of R and Q
    private final ImmutableSet<FunctionSymbol> Rsignature;       // signature of R
    private volatile ImmutableSet<FunctionSymbol> defSymbolsOfR;        // the same as ruleMap.keySet();
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> ruleMap;
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> reverseRuleMap; // a map from symbols of rhs to rules (which have to read from right to left!),
                                                                            // collapsing rules can be found with the null-functionSymbol
    private volatile ImmutableTriple<ImmutableSet<Rule>, ImmutableMap<FunctionSymbol, FunctionSymbol>, ImmutableMap<Rule, List<Pair<Position, Rule>>>> dps;  // the dps of this TRS, the mapping from defs to tups and the detailed mapping from rules to dps
    /**
     * the method to compute usable rules (with or without active)
     *
     * FIXME: This does not belong to QTRSProblem but to an QDPProblem. Reasons:
     *  - Usable Rules are not a property of a TRS but of a Dependency Pair
     *    Problem
     *  - QUsableRules references the QTRSProblem, so there are circular
     *    references
     * Fixing this is not so easy, as all places using QTRSProblem needs to be
     * investigated. But for most QTRSes the usable rules are not needed, so we
     * can generate them on demand.
     */
    private volatile QUsableRules qUsableRules = null;
    private volatile RelQUsableRules relqUsableRules = null;
    private volatile Wrapper<QApplicativeUsableRules> applicativeInfo;
    private volatile YNM isRRRQreducable;

    private static boolean checkConstructorArgs(final ImmutableSet<Rule> R, final QTermSet Q, final boolean QsuperR) {
        if (R == null || Q == null) {
            return false;
        }

        // check for proper QsuperR flag.
        return QsuperR == Q.canAllLhsBeRewritten(R);
    }

    /**
     * creates a TRS problem.
     * @param R - the TRS
     * @param Q - the lhs's of Q where every term is in standard numbering
     * @param QsuperR - the flag whether Q is a superset of the LHSs of R.
     * @param isRRRQreducable - a cached value whether some lhs of R is Q-reducable below the root
     */
    private QTRSProblem(final ImmutableSet<Rule> R, final QTermSet Q, final boolean QsuperR, final YNM isRRRQreducable, final QUsableRules qUsableRules) {
        super("QTRS", "Q restricted TRS");
        assert(QTRSProblem.checkConstructorArgs(R, Q, QsuperR));
        assert(isRRRQreducable != null);
        this.R = R;
        this.Q = Q;
        this.hashCode = this.R.hashCode()*849033+this.Q.hashCode()*84903+8490213;
        this.QsuperR = QsuperR;
        this.critPairs = null;
        this.maxArity = null;
        this.defSymbolsOfR = null;
        this.ruleMap = null;
        this.reverseRuleMap = null;
        this.applicativeInfo = null;
        this.isRRRQreducable = isRRRQreducable;
        this.qUsableRules = qUsableRules;
        Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.R);
        this.Rsignature = ImmutableCreator.create(signature);
        // create a copy
        signature = new LinkedHashSet<FunctionSymbol>(signature);
        signature.addAll(Q.getSignature());
        this.signature = ImmutableCreator.create(signature);
        this.calculateDefSymbolsAndRuleMap();
    }

    /**
     * creates a TRS problem from another one by just changing Q
     * @param qtrs
     * @param Q
     */
    private QTRSProblem(final QTRSProblem qtrs, final QTermSet Q) {
        super("QTRS", "Q restricted TRS");
        this.R = qtrs.R;
        this.Q = Q;
        this.hashCode = this.R.hashCode()*849033+this.Q.hashCode()*84903+8490213;
        this.QsuperR = this.Q.canAllLhsBeRewritten(this.R);
        this.critPairs = qtrs.getCriticalPairs(); // enforces sharing
        Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.R);
        // create a copy
        signature = new LinkedHashSet<FunctionSymbol>(signature);
        signature.addAll(Q.getSignature());
        this.signature = ImmutableCreator.create(signature);
        this.Rsignature = qtrs.Rsignature;
        this.defSymbolsOfR = qtrs.defSymbolsOfR;
        this.ruleMap = qtrs.ruleMap;
        this.reverseRuleMap = qtrs.reverseRuleMap;
        this.applicativeInfo = null;
        this.isRRRQreducable = YNM.MAYBE;
    }

    @Override
    public QTRSProblem maybeCopy() {
        return new QTRSProblem(this, this.Q);
    }

    /**
     * creates a new TRS-Problem for the given collection of Rules,
     * Q will be empty
     * @param R
     */
    public static QTRSProblem create(final ImmutableSet<Rule> R) {
        return QTRSProblem.create(R, new QTermSet(new ArrayList<TRSFunctionApplication>(0)));
    }

    @Override
    public ObligationType getObligationType() {
        return ObligationType.TRS;
    }

    /**
     * creates a new TRS-Problem for the given collection of Rules for R and Q
     * @param R
     * @param Q_it
     */
    public static QTRSProblem create(final ImmutableSet<Rule> R, final Iterable<TRSFunctionApplication> Q_it) {
        return QTRSProblem.create(R, new QTermSet(Q_it));
    }

    /**
     * creates a new TRS-Problem for the given collection of Rules for R and Q
     * @param R_it
     * @param Q
     */
    public static QTRSProblem create(final ImmutableSet<Rule> R, final QTermSet Q) {
        final boolean QsuperR = Q.canAllLhsBeRewritten(R);
        return new QTRSProblem(R, Q, QsuperR, YNM.MAYBE, null);
    }



    @Override
    public boolean equals(final Object oth) {
        if (this == oth) {
            return true;
        }

        if (oth == null) {
            return false;
        }

        if (oth.getClass() != this.getClass()) {
            return false;
        }

        final QTRSProblem other = (QTRSProblem) oth;
        if (!this.R.equals(other.R)) {
            return false;
        }

        return this.Q.equals(other.Q);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }


    public ImmutableSet<Rule> getR() {
        return this.R;
    }

    public QTermSet getQ() {
        return this.Q;
    }

    /**
     * Checks whether the set of normal forms w.r.t. Q is a <b>subset</b> of
     * the normal forms of R.
     * <p>
     * If this is true, each innermost rewrite step is also a Q rewrite step.
     * <p>
     * Therefore, if the TRS terminates with the innermost rewrite relation,
     * it also terminates with the Q rewrite relation.
     */
    public boolean QsupersetOfLhsR() {
        return this.QsuperR;
    }

    /**
     * Checks whether the set of normal forms w.r.t. Q is equal to the set of
     * normal forms of R.
     * <p>
     * If this is true, the innermost rewrite relation and the Q rewrite
     * relation are the same.
     */
    public boolean isExactlyInnermost() {
        if (this.QsuperR) {
            final Map<FunctionSymbol, ImmutableSet<Rule>> map = this.getRuleMap();
            ft: for (final TRSFunctionApplication ft : this.Q.getTerms()) {
                final Set<Rule> candidates = map.get(ft.getRootSymbol());
                if (candidates == null) {
                    return false;
                }
                for (final GeneralizedRule rule : candidates) {
                    if (rule.getLeft().matches(ft)) {
                        continue ft;
                    }
                }
                // no rule matches, so we have redex ft of Q, that is no redex of R
                return false;
            }
            // all redexes of Q are redexes of R
            // (with QsuperR => innermost)
            return true;
        } else {
            return false;
        }
    }

    public QUsableRules getQUsableRulesCalculator() {
        if (this.qUsableRules == null) {
            synchronized (this) {
                if (this.qUsableRules == null) {
                    this.qUsableRules = new QUsableRules(this);
                }
            }
        }
        return this.qUsableRules;
    }

    public RelQUsableRules getRelQUsableRulesCalculator() {  // TODO: this is really lame
        if (this.qUsableRules == null) {
            synchronized (this) {
                if (this.relqUsableRules == null) {
                    this.relqUsableRules = new RelQUsableRules(this);
                }
            }
        }
        return this.relqUsableRules;
    }

    public CriticalPairs getCriticalPairs() {
        if (this.critPairs == null) {
            synchronized (this) {
                if (this.critPairs == null) {
                    this.critPairs = new CriticalPairs(this);
                }
            }
        }
        return this.critPairs;
    }

    private void calculateDefSymbolsAndRuleMap() {
        final Map<FunctionSymbol, Set<Rule>> ruleMap = new LinkedHashMap<FunctionSymbol, Set<Rule>>();
        for (final Rule rule : this.R) {
            final FunctionSymbol f = rule.getRootSymbol();
            Set<Rule> fRules = ruleMap.get(f);
            if (fRules == null) {
                fRules = new LinkedHashSet<Rule>();
                ruleMap.put(f, fRules);
            }
            fRules.add(rule);
        }
        // make immutable
        final Map<FunctionSymbol, ImmutableSet<Rule>> immutableMap = new LinkedHashMap<FunctionSymbol, ImmutableSet<Rule>>();
        for (final Map.Entry<FunctionSymbol, Set<Rule>> entry : ruleMap.entrySet()) {
            immutableMap.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }
        this.ruleMap = ImmutableCreator.create(immutableMap);
        this.defSymbolsOfR = ImmutableCreator.create(immutableMap.keySet());
    }

    /**
     * get R as a mapping from defined symbols to corresponding rules
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> getRuleMap() {
        if (this.ruleMap == null) {
            synchronized(this) {
                if (this.ruleMap == null) {
                    this.calculateDefSymbolsAndRuleMap();
                }
            }
        }
        return this.ruleMap;
    }

    private void calculateReverseRuleMap() {
        final Map<FunctionSymbol, Set<Rule>> reverseRuleMap = Rule.getReversedRuleMap(this.R);
        final Map<FunctionSymbol, ImmutableSet<Rule>> immutableMap = new LinkedHashMap<FunctionSymbol, ImmutableSet<Rule>>();
        for (final Map.Entry<FunctionSymbol, Set<Rule>> entry : reverseRuleMap.entrySet()) {
            immutableMap.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }
        this.reverseRuleMap = ImmutableCreator.create(immutableMap);
    }

    /**
     * returns whether R has at least one collapsing rule;
     * @return
     */
    public boolean isCollapsing() {
        return this.getReverseRuleMap().containsKey(null);
    }

    /**
     * get R^{-1} as a mapping from function symbols of rhs to corresponding rules.
     * Note that the rules a still from left to right, i.e. one has to read the rules
     * reversed!
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> getReverseRuleMap() {
        if(this.reverseRuleMap == null) {
            synchronized(this) {
                if(this.reverseRuleMap == null) {
                    this.calculateReverseRuleMap();
                }
            }
        }
        return this.reverseRuleMap;
    }

    private final static ImmutableSet<Rule> EMPTYSET = ImmutableCreator.create(java.util.Collections.<Rule>emptySet());

    /**
     * get all collapsing rules, i.e. where the rhs is a variable
     */
    public ImmutableSet<Rule> getCollapsingRules() {
        final ImmutableSet<Rule> res = this.getReverseRuleMap().get(null);
        return res == null ? QTRSProblem.EMPTYSET : res;
    }

    public ImmutableSet<FunctionSymbol> getDefinedSymbolsOfR() {
        return this.defSymbolsOfR;
    }

    public ImmutableSet<FunctionSymbol> getSignature() {
        return this.signature;
    }

    public ImmutableSet<FunctionSymbol> getRSignature() {
        return this.Rsignature;
    }

    /**
     * returns the set of DPs of this TRS
     */
    public ImmutableTriple<ImmutableSet<Rule>, ImmutableMap<FunctionSymbol, FunctionSymbol>, ImmutableMap<Rule, List<Pair<Position, Rule>>>> getDPs() {
        if (this.dps == null) {
            synchronized(this) {
                if (this.dps == null) {
                    final Map<Rule, List<Pair<Position, Rule>>> dpMap = new LinkedHashMap<Rule, List<Pair<Position, Rule>>>();
                    final Set<Rule> dps = new LinkedHashSet<Rule>();
                    final Set<FunctionSymbol> signature = new LinkedHashSet<FunctionSymbol>(this.getSignature());
                    final Set<FunctionSymbol> defs = this.getDefinedSymbolsOfR();
                    final Map<FunctionSymbol, FunctionSymbol> defToTup = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();

                    for (final Rule rule : this.R) {
                        final List<Pair<TRSFunctionApplication,Position>> dpRhss = new ArrayList<Pair<TRSFunctionApplication, Position>>();
                        final TRSFunctionApplication lhs = rule.getLeft();
                        final TRSTerm rhs = rule.getRight();
                        // get all subterms of rhs of actRule which have a defined symbol as root
                        for (final Pair<Position, TRSTerm> posAndSubterm : rhs.getPositionsWithSubTerms()) {
                            final TRSTerm subterm = posAndSubterm.y;
                            if (!subterm.isVariable()) {
                                final TRSFunctionApplication ft = (TRSFunctionApplication) subterm;
                                final FunctionSymbol actFuncSym = ft.getRootSymbol();
                                if(defs.contains(actFuncSym)) {
                                    if (!lhs.hasProperSubterm(subterm)) {
                                        dpRhss.add(new Pair<TRSFunctionApplication,Position>(ft,posAndSubterm.x));
                                    }
                                }
                            }
                        }

                        if (dpRhss.isEmpty()) {
                            continue;
                        }

                        final FunctionSymbol tf = QTRSProblem.getTupleSymbol(lhs.getRootSymbol(), defToTup, signature);
                        final TRSFunctionApplication tlhs = TRSTerm.createFunctionApplication(tf, lhs.getArguments());
                        final List<Pair<Position, Rule>> posDPlist = new ArrayList<Pair<Position, Rule>>(dpRhss.size());

                        for (final Pair<TRSFunctionApplication,Position> posAndDpRhs : dpRhss) {
                            final TRSFunctionApplication dpRhs = posAndDpRhs.x;
                            final FunctionSymbol tg = QTRSProblem.getTupleSymbol(dpRhs.getRootSymbol(), defToTup, signature);
                            final TRSFunctionApplication trhs = TRSTerm.createFunctionApplication(tg, dpRhs.getArguments());
                            final Rule dp = Rule.create(tlhs, trhs);
                            posDPlist.add(new Pair<Position,Rule>(posAndDpRhs.y, dp));
                            dps.add(dp);
                        }

                        dpMap.put(rule, posDPlist);
                    }

                    this.dps = new ImmutableTriple<ImmutableSet<Rule>, ImmutableMap<FunctionSymbol, FunctionSymbol>, ImmutableMap<Rule, List<Pair<Position, Rule>>>>(
                            ImmutableCreator.create(dps),
                            ImmutableCreator.create(defToTup),
                            ImmutableCreator.create(dpMap)
                            );
                }
            }
        }
        return this.dps;
    }

    /**
     * looksup a tuple symbol for a defined symbol f. If it is not defined, a new symbol is created (which is not
     * contained in allSyms) and the mapping is stored, and the new symbol is added to allSyms
     * @param f
     * @param defToTup
     * @param allSyms
     * @return
     */
    //TODO: Change this place to a different more suitable place/class
    public static FunctionSymbol getTupleSymbol(final FunctionSymbol f, final Map<FunctionSymbol, FunctionSymbol> defToTup, final Set<FunctionSymbol> allSyms) {
        FunctionSymbol tf = defToTup.get(f);
        if (tf == null) {
            final String wishedName = f.getName().toUpperCase();
            final int arity = f.getArity();
            int nr = 1;
            tf = FunctionSymbol.create(wishedName, arity);
            while (!allSyms.add(tf)) {
                tf = FunctionSymbol.create(wishedName+"^"+nr, arity);
                nr++;
            }

            defToTup.put(f, tf);
        }
        return tf;
    }

    private final Object recursiveLock = new Object();
    private Set<FunctionSymbol> recursiveSymbols;

    public boolean isRecursive(final FunctionSymbol symbol) {
        synchronized(this.recursiveLock) {
            if (this.recursiveSymbols == null) {
                // first compute the "dependency" graph
                // where there is an edge from g -> f iff a g-rule contains f in its rhs.
                final Map<FunctionSymbol,ImmutableSet<Rule>> ruleMap = this.getRuleMap();
                final Map<FunctionSymbol,Node<FunctionSymbol>> gMap = new HashMap<FunctionSymbol, Node<FunctionSymbol>>();
                final SimpleGraph<FunctionSymbol,?> depGraph = new SimpleGraph<FunctionSymbol,Object>();
                for (final FunctionSymbol g : ruleMap.keySet()) {
                    final Node<FunctionSymbol> n = new Node<FunctionSymbol>(g);
                    depGraph.addNode(n);
                    gMap.put(g, n);
                }
                final Set<FunctionSymbol> rhsSyms = new HashSet<FunctionSymbol>();
                for (final Map.Entry<FunctionSymbol, ImmutableSet<Rule>> gRules : ruleMap.entrySet()) {
                    rhsSyms.clear();
                    final Node<FunctionSymbol> gn = gMap.get(gRules.getKey());
                    for (final Rule rule : gRules.getValue()) {
                        for (final FunctionSymbol f : rule.getRight().getFunctionSymbols()) {
                            if (rhsSyms.add(f)) { // if f has not been seen up to now
                                final Node<FunctionSymbol> fn = gMap.get(f);
                                if (fn != null) {
                                    depGraph.addEdge(gn, fn);
                                } // otherwise it was a constructor!
                            }
                        }
                    }
                }

                // now the dep-graph is created
                // let us determine which functions are non-recursive.
                // i.e. which do not (transitively) call a recursive function.
                final Set<FunctionSymbol> recursive = new LinkedHashSet<FunctionSymbol>();
                final ArrayStack<Node<FunctionSymbol>> todo = new ArrayStack<Node<FunctionSymbol>>();
                for (final Cycle<FunctionSymbol> SCC : depGraph.getSCCs()) {
                    for (final Node<FunctionSymbol> rn : SCC) {
                        todo.push(rn);
                        recursive.add(rn.getObject());
                    }
                }

                // now go backwards!
                while (!todo.isEmpty()) {
                    final Node<FunctionSymbol> rn = todo.pop();
                    for (final Node<FunctionSymbol> pn : depGraph.getIn(rn)) {
                        if (recursive.add(pn.getObject())) {
                            todo.push(pn);
                        }
                    }
                }

                // and set result
                this.recursiveSymbols = recursive;

            }
            return this.recursiveSymbols.contains(symbol);
        }
    }

    /**
     * get the Applicative Info.
     * returns null if this signature is not applicative
     */
    public QApplicativeUsableRules getApplicativeInfo() {
        if (this.applicativeInfo == null) {
            synchronized(this) {
                if (this.applicativeInfo == null) {
                    QApplicativeUsableRules qaur;
                    if (QApplicativeUsableRules.applicativeSignature(this.getSignature())) {
                        qaur = new QApplicativeUsableRules(this);
                    } else {
                        qaur = null;
                    }
                    this.applicativeInfo = new Wrapper<QApplicativeUsableRules>(qaur);
                }
            }
        }
        return this.applicativeInfo.x;
    }

    /**
     * returns the A-Transformed Q-TRS, or null, if it is not a-transformable
     */
    public QTRSProblem getATransformed() {
        final QApplicativeUsableRules qaur = this.getApplicativeInfo();
        if (qaur == null) {
            return null;
        } else {
            final Pair<QTRSProblem,?> result = qaur.getATransformedQTRS(this.R);
            if (result == null) {
                return null;
            } else {
                return result.x;
            }
        }
    }

    /**
     * checks whether a lhs of R contains a Q redex below the root
     * @return
     */
    public boolean isRRRQreducable() {
        if (this.isRRRQreducable == YNM.MAYBE) {
            synchronized(this) {
                if (this.isRRRQreducable == YNM.MAYBE) {
                    if (!this.Q.isEmpty()) {
                        for (final Rule rule : this.R) {
                            for (final TRSTerm subTerm : rule.getLeft().getArguments()) {
                                if (this.Q.canBeRewritten(subTerm)) {
                                    this.isRRRQreducable = YNM.YES;
                                    return true;
                                }
                            }
                        }
                    }
                    this.isRRRQreducable = YNM.NO;
                }
            }
        }
        return this.isRRRQreducable.toBool();
    }

    /**
     * set the RRR-Q reducable flag by hand
     * @param value
     */
    public void setRRRQreducable(final boolean value) {
        if (Globals.useAssertions) {
            assert(this.isRRRQreducable() == value);
        }
        this.isRRRQreducable = YNM.fromBool(value);
    }

    /**
     * @return Maximal arity of signature
     */
    public int getMaxArity() {
        if(this.maxArity == null) {
            int max =0;
            for(final FunctionSymbol fs : this.getSignature()) {
                final int arity = fs.getArity();
                if (arity > max) {
                    max = arity;
                }
            }
            this.maxArity = max;
        }
        return this.maxArity;
    }

    /**
     * returns the set of terms in R and Q,
     * the set may be modified
     */
    @Override
    public Set<TRSTerm> getTerms() {
        // terms of R
        final Set<TRSTerm> terms = CollectionUtils.getTerms(this.R);
        // plus terms of Q
        terms.addAll(this.Q.getTerms());
        return terms;
    }

    /**
     * creates a QTRS from this one with different Q
     * @param Q
     */
    public QTRSProblem create(final QTermSet Q) {
        if (Q.getTerms().equals(this.Q.getTerms())) {
            return this;
        }
        return new QTRSProblem(this, Q);
    }

    /**
     * creates a QTRS where Q is set to innermost strategy
     */
    public QTRSProblem createInnermost() {
        final QTermSet Q = new QTermSet(CollectionUtils.getLeftHandSides(this.R));
        return this.create(Q);
    }

    /**
     * creates a QTRS where Q is set to empty set
     */
    public QTRSProblem createTermination() {
        final QTermSet Q = new QTermSet(new LinkedList<TRSFunctionApplication>());
        return this.create(Q);
    }



    /**
     * creates a sub problem with less rules in R
     * @param rules
     * @return
     */
    public QTRSProblem createSubProblem(final ImmutableSet<Rule> rules) {
        if (Globals.useAssertions) {
            assert(this.R.containsAll(rules));
        }
        boolean qSuperR = this.QsuperR;
        if (!qSuperR) {
            qSuperR = this.Q.canAllLhsBeRewritten(rules);
        }
        final YNM isRRRQreducable = (YNM) this.isRRRQreducable.and(YNM.MAYBE);
        return new QTRSProblem(rules, this.Q, qSuperR, isRRRQreducable, null);
    }

    /**
     * creates a sub problem where the new R are the usable rules of the given
     * DP problem qdp. The qdp must be innermost!
     * @param qdp
     */
    public QTRSProblem createUsableRulesSubProblem(final QDPProblem qdp) {
        final ImmutableSet<Rule> usableRules = qdp.getUsableRules();
        if (Globals.useAssertions) {
            assert(qdp.getRwithQ() == this);
            assert(qdp.QsupersetOfLhsR());
        }
        if (this.R.size() == usableRules.size()) {
            if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                System.err.println("Warning: createUsableRulesSubProblem in QTRS produces identity");
            }
            return this;
        }
        final boolean qSuperR = true;
        final YNM isRRRQreducable = (YNM) this.isRRRQreducable.and(YNM.MAYBE);
        return new QTRSProblem(usableRules, this.Q, qSuperR, isRRRQreducable, this.getQUsableRulesCalculator());
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder s = new StringBuilder();
        s.append(o.export("Q restricted rewrite system:"));
        s.append(o.cond_linebreak());
        if (this.R.isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.R, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        if (this.Q.getTerms().isEmpty()) {
            s.append("Q is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The set Q consists of the following terms:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.Q.getTerms(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        return s.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

    @Override
    public String toExternString() {
        final TRSGenerator trsGen =  new TRSGenerator();
        trsGen.writeRules(this.R);
        if (! this.Q.isEmpty()) {
            // be compatible to the competition format if there is no Q anyway
            trsGen.writeQ(this.Q.getTerms());
        }
        return trsGen.getTRSString(false, null);
    }

    @Override
    public String externName() {
        return "trs";
    }

    public boolean isRightGround() {
        for (final Rule rule : this.getR()) {
            if (!rule.getRight().getVariables().isEmpty()) {
                return false;
            }
        }
        return true;
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element e = XMLTag.QTRS_OBL.createElement(doc);
        final Element f = XMLTag.QTRS.createElement(doc);

        final Element trs = XMLTag.TRS.createElement(doc);
        CollectionUtils.addChildren(this.R, trs, doc, xmlMetaData);
        f.appendChild(trs);

        f.appendChild(this.Q.toDOM(doc, xmlMetaData));

        final Element innermost = XMLTag.INNERMOST.createElement(doc);
        if (!this.QsupersetOfLhsR()) {
            if (this.isExactlyInnermost()) {
                XMLAttribute.EXACTLY_INNERMOST.setAttribute(innermost, "true");
                f.appendChild(innermost);
            }
        } else {
            if (this.isExactlyInnermost()) {
                XMLAttribute.EXACTLY_INNERMOST.setAttribute(innermost, "true");
                f.appendChild(innermost);
            } else {
                XMLAttribute.EXACTLY_INNERMOST.setAttribute(innermost, "false");
                f.appendChild(innermost);
            }
        }

        final Element sig = XMLTag.SIGNATURE.createElement(doc);
        CollectionUtils.addChildren(this.getSignature(), sig, doc, xmlMetaData);
        f.appendChild(sig);

        e.appendChild(f);
        return e;
    }

    @Override
    public Element getCPFInput(final Document doc, final XMLMetaData xmlMetaData, final TruthValue tv) {
        final Element trsInput = CPFTag.TRS_INPUT.create(doc,
                CPFTag.trs(doc, xmlMetaData, this.getR()));

        final Element strategy = CPFTag.STRATEGY.createElement(doc);
        if (!this.QsupersetOfLhsR()) {
            if (this.isExactlyInnermost()) {
                strategy.appendChild(CPFTag.INNERMOST.createElement(doc));
                trsInput.appendChild(strategy);
            }
        } else {
            if (this.isExactlyInnermost()) {
                strategy.appendChild(CPFTag.INNERMOST.createElement(doc));
                trsInput.appendChild(strategy);
            } else {
                strategy.appendChild(this.getQ().toCPF(doc, xmlMetaData));
                trsInput.appendChild(strategy);
            }
        }
        return trsInput;
    }

    @Override
    public Element getCPFAssumption(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final CPFModus modus,
        final TruthValue tv)
    {
        if (modus.isPositive()) {
            return CPFTag.TRS_TERMINATION_PROOF.create(
                doc,
                CPFTag.TERMINATION_ASSUMPTION.create(doc, this.getCPFInput(doc, xmlMetaData, tv)));
        } else {
            return CPFTag.TRS_NONTERMINATION_PROOF.create(
                doc,
                CPFTag.NONTERMINATION_ASSUMPTION.create(doc, this.getCPFInput(doc, xmlMetaData, tv)));
        }
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination w.r.t. Q");
    }

    @Override
    public FeatureVector<Features> getFeatureVector() {
        return FeaturesQTRS.getFeatures(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        if (this.getMaxArity() <= 1) {
            return "qsrs";
        } else {
            return "qtrs";
        }
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.BasicObligation.DefaultBasicObligation#offersCertifiableTechniques()
     */
    @Override
    public boolean offersCertifiableTechniques() {
        return true;
    }

}
