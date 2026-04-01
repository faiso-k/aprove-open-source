/*
 * Created on 11.04.2005
 */
package aprove.verification.dpframework.DPProblem;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.AFSPrecalculation.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.Graph.Node;
import aprove.verification.oldframework.Utility.Profiling.*;
import aprove.verification.oldframework.Utility.Profiling.FeaturesQDP.*;
import aprove.xml.*;
import immutables.*;

/**
 * Use getSubProblem...(...) whenever you need a DP problem that has
 * some aspects in common with your current DP problem. Then some of
 * the internal immutable data structures can and will be shared,
 * and efficiency is improved.
 *
 * @author thiemann
 * @version $Id$
 */
public final class QDPProblem extends DefaultBasicObligation implements
        Immutable, HTML_Able, HasTRSTerms, ExternUsable, XMLObligationExportable,
        DOT_Able,
        HasFeatureVector<FeaturesQDP.Features>
{

    /*
     * real values
     */
    private final boolean minimal;
    private final QDependencyGraph graph;
    private final QTRSProblem rWithQ;

    /*
     * computes / cached values
     */
    private final int hashCode;
    private final ImmutableSet<Rule> P;

    private volatile ImmutableSet<Rule> usableRules;

    private volatile ImmutableSet<FunctionSymbol> signature;
    private volatile ImmutableSet<FunctionSymbol> PRsignature;
    private volatile ImmutableSet<FunctionSymbol> headSymbols;

    private volatile Wrapper<QApplicativeUsableRules> applicativeInfo;

    private volatile YNM isRRRQreducable;

    private final Object afsLock = new Object();
    private volatile AbortableIterable<Pair<Map<FunctionSymbol, YNM[]>, Set<? extends GeneralizedRule>>> afsEnumerator; // all possible AFS that produce TRSs as (active) usable rules
    private volatile int afsEnumeratorRestriction;       // last restriction on the number of arguments that each
                                                // function symbol may keep
    private Integer maxArity;

    /**
     * Remember the constraints that are computed for this QDPProblem.
     */
    private final ConstraintsCache<Rule> constraintsCache;

    /**
     * creates a QDP-problem.
     * @param rWithQ
     * @param graph - the graph should be the (P,Q,R) dependency graph
     * @param minimal
     * @param isRRRQreducable - a YNM indicating whether the lhs of R or P can
     * be Q reduced (for R below the root)
     * @param constraintsCache The cache for constraints associated with this
     * QDPProblem, null means 'not computed yet'.
     */
    private QDPProblem(final QTRSProblem rWithQ,
            final QDependencyGraph graph,
            final boolean minimal,
            final YNM isRRRQreducable,
            final ConstraintsCache<Rule> constraintsCache) {
        super("QDP", "Q-DP-Problem");
        if (Globals.useAssertions) {
            assert (rWithQ != null && graph != null);
        }
        // the line below ensures that one cannot use
        // usable rules in rainbow proofs
        // (since they are currently not supported)
        this.minimal = (Options.certifier.isRainbow()) ? false : minimal;
        this.rWithQ = rWithQ;
        this.P = graph.getP();
        this.graph = graph;
        this.usableRules = ImmutableCreator.create(this.getQUsableRulesCalculator().getUsableRules(this.P));
        this.signature = null;
        this.PRsignature = null;
        QApplicativeUsableRules qaur =
            this.rWithQ.getApplicativeInfo();
        if (qaur != null
            && !QApplicativeUsableRules.applicativeRules(this.P)) {
            qaur = null;
        }
        this.applicativeInfo =
            new Wrapper<QApplicativeUsableRules>(qaur);
        this.afsEnumerator = null;
        this.headSymbols = null;
        this.hashCode = 8831123*this.P.hashCode() + 1293527*rWithQ.hashCode()
            + (minimal ? 7553901 : 89043284);
        this.isRRRQreducable = isRRRQreducable;
        if (this.isRRRQreducable == YNM.MAYBE) {
            final QTermSet Q = this.getQ();
            if (!Q.isEmpty()) {
                if (this.rWithQ.isRRRQreducable()) {
                    this.isRRRQreducable = YNM.YES;
                }

                for (final Rule rule : this.P) {
                    if (Q.canBeRewritten(rule.getLeft())) {
                        this.isRRRQreducable = YNM.YES;
                    }
                }
            }
            this.isRRRQreducable = YNM.NO;
        }
        this.maxArity = null;
        this.constraintsCache = constraintsCache;
        if (this.constraintsCache == null) {
            throw new RuntimeException("ConstraintsChache should be an emptyConstraintsCache and not null");
        }
        this.computeSignatures();
    }

    /**
     * create a new DP problem from a given graph P over rules (the pairs), the TRS R and the minimal flag.
     * Note that P will be modified!
     * @param P
     * @param rWithQ
     * @param minimal
     * @return
     */
    public static QDPProblem create(final Graph<Rule, ?> P, final QTRSProblem rWithQ, final boolean minimal) {
        final QDependencyGraph graph = QDependencyGraph.create(P, rWithQ);
        return new QDPProblem(rWithQ, graph, minimal, YNM.MAYBE,
            ConstraintsCache.emptyConstraintsCache);
    }

    public static QDPProblem create(final Set<Rule> P, final QTRSProblem rWithQ, final boolean minimal) {
        final QDependencyGraph graph = QDependencyGraph.create(P, rWithQ);
        return new QDPProblem(rWithQ, graph, minimal, YNM.MAYBE, ConstraintsCache.emptyConstraintsCache);
    }

    public static QDPProblem create(final QTRSProblem rWithQ, final QDependencyGraph graph, final boolean minimal, final boolean isRRRQreducable) {
        final YNM isReducable = YNM.fromBool(isRRRQreducable);
        return new QDPProblem(rWithQ, graph, minimal, isReducable, ConstraintsCache.emptyConstraintsCache);
    }

    /**
     * returns a subproblem with smaller P
     */
    public QDPProblem getSubProblem(final ImmutableSet<Rule> P) {
        return this.getSubProblem(this.graph.getSubGraphFromPRules(P));
    }


    /**
     * returns a subproblem with smaller graph
     * @param graph
     * @return
     */
    public QDPProblem getSubProblem(final QDependencyGraph graph) {
        if (Globals.useAssertions) {
            assert (this.graph.getGraph().getNodes().containsAll(graph.getGraph().getNodes()));
            assert (this.graph.getGraph().getEdges().containsAll(graph.getGraph().getEdges()));
        }
        YNM isRRRQreducable = this.isRRRQreducable;
        if (isRRRQreducable == YNM.YES) {
            // only switch to maybe if a known redex is in P
            // because otherwise we have and keep a redex in R
            if (!this.rWithQ.isRRRQreducable()) {
                isRRRQreducable = YNM.MAYBE;
            }
        }

        ConstraintsCache<Rule> newCache = null;
        if (this.constraintsCache != null) {
            // The cache already contained precomputed constraints, so make use
            // of this information by adapting the cache for the new QDPProblem.
            newCache = this.constraintsCache.fromGraph(graph);
        }
        return new QDPProblem(this.rWithQ, graph, this.minimal, isRRRQreducable,
                newCache);
    }

    @Override
    public ObligationType getObligationType() {
        return ObligationType.DP;
    }

    /**
     * returns the same problem with a possible different minimality flag
     */
    public QDPProblem getSameProblem(final boolean minimality) {
        // No rule is changed, so the cache stays valid.
        return new QDPProblem(this.rWithQ, this.graph, minimality,
                this.isRRRQreducable, this.constraintsCache);
    }

    /**
     * returns the same problem with new ConstraintsCache
     */
    public QDPProblem getSameProblemAndFillCache(final ConstraintsCache<Rule> constraintsCache) {
        // Insert constraint information into the cache.
        return new QDPProblem(this.rWithQ, this.graph, this.minimal,
                this.isRRRQreducable, constraintsCache);
    }

    /**
     * returns a subproblem with R replaced by usable rules. (only in innermost case)
     * this method allows to carry over the usable rule calculation
     * (in contrast to getSubProblemWithSmallerR)
     */
    public QDPProblem getSubProblemWithUsableRules() {
        final QTRSProblem rWithQ = this.rWithQ.createUsableRulesSubProblem(this);
        final QDependencyGraph subGraph = this.graph.getUsableRulesSubGraph(rWithQ);
        YNM isRRRQreducable = this.isRRRQreducable;
        if (isRRRQreducable == YNM.YES) {
            // only switch to maybe if a known redex is in R
            // because otherwise we have and keep a redex in P
            if (this.rWithQ.isRRRQreducable()) {
                isRRRQreducable = YNM.MAYBE;
            }
        }
        // TODO Is it valid to retain the cache, because nothing
        // of interest is changed?
        return new QDPProblem(rWithQ, subGraph, this.minimal, isRRRQreducable,
                ConstraintsCache.emptyConstraintsCache);
    }

    /**
     * returns a subproblem with smaller R.
     * Note that unlike getSubProblemWithUsableRules,
     * here the usable-rule calculation cannot be reused.
     */
    public QDPProblem getSubProblemWithSmallerR(final ImmutableSet<Rule> R) {
        if (Globals.useAssertions) {
            assert (this.rWithQ.getR().containsAll(R));
        }
        final QTRSProblem rWithQ = this.rWithQ.createSubProblem(R);
        final QDependencyGraph subGraph = this.graph.getSubGraph(this.P, rWithQ);
        YNM isRRRQreducable = this.isRRRQreducable;
        if (isRRRQreducable == YNM.YES) {
            // only switch to maybe if a known redex is in R
            // because otherwise we have and keep a redex in P
            if (this.rWithQ.isRRRQreducable()) {
                isRRRQreducable = YNM.MAYBE;
            }
        }
        return new QDPProblem(rWithQ, subGraph, this.minimal, isRRRQreducable,
                ConstraintsCache.emptyConstraintsCache);
    }

    /**
     * returns a subproblem with irrelevant Q-terms removed
     */
    public QDPProblem getSubProblemWithSmallerQ(final QTermSet Q, final boolean newMinimality) {
        final QTRSProblem rWithQ = this.rWithQ.create(Q);
        final QDependencyGraph subGraph = this.graph.getSubGraph(this.P, rWithQ);
        YNM isRRRQreducable = this.isRRRQreducable;
        if (isRRRQreducable == YNM.YES) {
            // only switch to maybe if a known redex is in R
            // because otherwise we have and keep a redex in P
            if (this.rWithQ.isRRRQreducable()) {
                isRRRQreducable = YNM.MAYBE;
            }
        }
        return new QDPProblem(rWithQ, subGraph, newMinimality, isRRRQreducable,
                ConstraintsCache.emptyConstraintsCache);
    }


    /**
     * returns a subproblem with smaller P and R
     */
    public QDPProblem getSubProblem(final Set<Rule> P, final ImmutableSet<Rule> R) {
        if (Globals.useAssertions) {
            assert (this.rWithQ.getR().containsAll(R) && this.P.containsAll(P));
        }
        final QTRSProblem rWithQ = this.rWithQ.createSubProblem(R);
        final QDependencyGraph subGraph = this.graph.getSubGraph(P, rWithQ);
        this.isRRRQreducable = (YNM) this.isRRRQreducable.and(YNM.MAYBE);
        // TODO Maybe update the cache when R is not altered?
        // See getSubProblem(QDependencyGraph graph).
        return new QDPProblem(rWithQ, subGraph, this.minimal, this.isRRRQreducable,
                ConstraintsCache.emptyConstraintsCache);
    }

    /**
     * switches from full termination to innermost termination.
     * @return
     */
    public QDPProblem getInnermostProblem() {
        if (Globals.useAssertions) {
            assert(!this.rWithQ.getR().isEmpty());
            assert(this.rWithQ.getQ().isEmpty());
        }
        final QTRSProblem rWithQ = this.rWithQ.createInnermost();
        final QDependencyGraph subGraph = this.graph.getSubGraph(this.P, rWithQ);
        // The rules are not altered, so the cache stays valid.
        return new QDPProblem(rWithQ, subGraph, this.minimal, YNM.MAYBE,
                this.constraintsCache);
    }

    /**
     * switches to full termination and removes minimality flag
     * @return
     */
    public QDPProblem getTerminationProblem() {
        if (Globals.useAssertions) {
            assert(!this.rWithQ.getQ().isEmpty());
        }
        final QTRSProblem rWithQ = this.rWithQ.createTermination();
        final QDependencyGraph subGraph = this.graph.getSubGraph(this.P, rWithQ);
        // The rules are not altered, so the cache stays valid.
        return new QDPProblem(rWithQ, subGraph, false, YNM.NO,
                this.constraintsCache);
    }

    /**
     * returns a new QDP-Problem where s_to_t is transformed by nri to a set of new
     * DPs. Moreover, the counter for the new DPs and the given transformation is returned.
     * @param s_to_t
     * @param newDPs
     * @param p the position of the transformation in t.
     * @return
     */
    public Pair<QDPProblem, Integer> getTransformedProblem(final QDPTransformation transformation, final Node<Rule> s_to_t, final Set<Rule> newDPs, final Position p) {
        final Pair<QDependencyGraph, Integer> graphCounter =
            this.graph.getTransformedGraph(transformation, s_to_t, newDPs, p);
        return new Pair<QDPProblem, Integer>(
                new QDPProblem(this.rWithQ, graphCounter.x, this.minimal,
                        YNM.MAYBE, ConstraintsCache.emptyConstraintsCache),
                graphCounter.y);
    }



    public QDependencyGraph getDependencyGraph() {
        return this.graph;
    }

    public ImmutableSet<Rule> getUsableRules() {
/*        if (this.usableRules == null) {
            // only synchronize if cache is not yet computed,
            // synchronize to omit multiple computation of usable rules
            synchronized(this.usableRulesLock) {
                if (this.usableRules == null) {
                    this.usableRules = ImmutableCreator.create(this.getQUsableRulesCalculator().getUsableRules(this.P));
                }
            }
        }
*/        return this.usableRules;
    }

    public QUsableRules getQUsableRulesCalculator() {
        return this.rWithQ.getQUsableRulesCalculator();
    }

    /**
     * get the Applicative Info to create a-transformed DP-problems. returns
     * null, if this QDP is not applicative
     */
    public QApplicativeUsableRules getApplicativeInfo() {
/*        if (this.applicativeInfo == null) {
            synchronized(this.applicativeInfoLock) {
                if (this.applicativeInfo == null) {
                    QApplicativeUsableRules qaur =
                        this.rWithQ.getApplicativeInfo();
                    if (qaur != null
                        && !QApplicativeUsableRules.applicativeRules(this.P)) {
                        qaur = null;
                    }
                    this.applicativeInfo =
                        new Wrapper<QApplicativeUsableRules>(qaur);
                }
            }
        }
*/        return this.applicativeInfo.x;
    }

    /**
     * @param j
     * @param i
     * @return The precomputed constraints cache (null if not already computed).
     */
    public ConstraintsCache<Rule> getConstraintsCache() {
        return this.constraintsCache;
    }


    /**
     * returns the A-Transformed Q-DP-Problem with given new minimality flag.
     * (a map from old DPs to a-transformed DP-s is given, as well as the a-transformed qtrs).
     * returns null, if this Q-DP-Problem is not a-transformable.
     */
    public Pair<Map<Rule,Rule>, QTRSProblem> getATransformed() {

        final QApplicativeUsableRules qaur = this.getApplicativeInfo();
        if (qaur == null) {
            return null;
        } else {
            return qaur.getATransformedQDP(this.P, this.getR());
        }
    }


    /**
     * checks whether a subterm of a lhs of R of a lhs of P contains a Q-redex
     * @return
     */
    public boolean isRRRQreducable() {
/*        if (this.isRRRQreducable == YNM.MAYBE) {
            synchronized(this.rrrQLock) {
                if (this.isRRRQreducable == YNM.MAYBE) {
                    final QTermSet Q = this.getQ();
                    if (!Q.isEmpty()) {
                        if (this.rWithQ.isRRRQreducable()) {
                            this.isRRRQreducable = YNM.YES;
                            return true;
                        }

                        for (final Rule rule : this.P) {
                            if (Q.canBeRewritten(rule.getLeft())) {
                                this.isRRRQreducable = YNM.YES;
                                return true;
                            }
                        }
                    }
                    this.isRRRQreducable = YNM.NO;
                }
            }
        }
*/        return this.isRRRQreducable.toBool();
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
     * returns the set of all terms in P,Q,R.
     * the resulting set may be safely modified.
     */
    @Override
    public Set<TRSTerm> getTerms() {
        final Set<TRSTerm> terms = CollectionUtils.getTerms(this.P);
        terms.addAll(this.rWithQ.getTerms());
        return terms;
    }

    /**
     * returns the signature of P cup R cup Q
     */
    public ImmutableSet<FunctionSymbol> getSignature() {
//        if (this.signature == null) {
//            computeSignatures();
//        }
        return this.signature;
    }

    /**
     * returns the signature of P cup R
     */
    public ImmutableSet<FunctionSymbol> getPRSignature() {
//        if (this.signature == null) {
//            computeSignatures();
//        }
        return this.PRsignature;
    }

    public ImmutableSet<FunctionSymbol> getHeadSymbols() {
//        if (this.signature == null) {
//            computeSignatures();
//        }
        return this.headSymbols;
    }

    private void computeSignatures() {
//        synchronized(this.signatureLock) {
//            if (this.signature == null) {
                final Set<FunctionSymbol> forbidden = new LinkedHashSet<FunctionSymbol>(this.rWithQ.getRSignature());
                final Set<FunctionSymbol> headSyms = new LinkedHashSet<FunctionSymbol>();
                // headSyms and forbidden are disjoint!
                // in the end, headSyms should contain the head syms of P,R
                // and forbidden is the remaining signature of P \cup R

                for (final Rule dp : this.P) {
                    final TRSFunctionApplication s = dp.getLeft();

                    // add non-root signature of s to forbidden
                    for (final TRSTerm arg : s.getArguments()) {
                        for (final FunctionSymbol f : arg.getFunctionSymbols()) {
                            if (forbidden.add(f)) {
                                headSyms.remove(f);
                            }
                        }
                    }

                    // add non-root signature of t to forbidden
                    final TRSTerm t = dp.getRight();
                    if (!t.isVariable()) {
                        final TRSFunctionApplication tt = (TRSFunctionApplication) t;
                        for (final TRSTerm arg : tt.getArguments()) {
                            for (final FunctionSymbol f : arg.getFunctionSymbols()) {
                                if (forbidden.add(f)) {
                                    headSyms.remove(f);
                                }
                            }
                        }

                        // add root-symbol of t
                        final FunctionSymbol f = tt.getRootSymbol();
                        if (!forbidden.contains(f)) {
                            headSyms.add(f);
                        }
                    }

                    // add root-symbol of s
                    final FunctionSymbol f = s.getRootSymbol();
                    if (!forbidden.contains(f)) {
                        headSyms.add(f);
                    }
                }

                forbidden.addAll(headSyms); // now forbidden = signature (P u R)

                final Set<FunctionSymbol> fullSignature = new LinkedHashSet<FunctionSymbol>(forbidden);
                fullSignature.addAll(this.getQ().getSignature());
                // and fullSignature = signature (P u R u Q)

                this.PRsignature = ImmutableCreator.create(forbidden);
                this.headSymbols = ImmutableCreator.create(headSyms);
                this.signature = ImmutableCreator.create(fullSignature);
//            }
//        }
    }


    /**
     * returns a set of all possible AFSs that lead to active usable rules which
     * form a TRS. Note that all AFSs will be stored, i.e. if it is clear that these
     * AFSs will no longer be needed, one should forget these AFSs by calling
     * <code>forgetAfsIterable</code>
     * @param restriction - a limit of arguments per function symbol, -1 means no limit.
     */
    public AbortableIterable<Pair<Map<FunctionSymbol, YNM[]>, Set<? extends GeneralizedRule>>> getAfsIterable(final int restriction, final boolean active) {
        synchronized(this.afsLock) {
            if (this.afsEnumerator == null || restriction != this.afsEnumeratorRestriction) {
                final AbortableIterator<Pair<Map<FunctionSymbol, YNM[]>, Set<? extends GeneralizedRule>>> iterator = new DynamicYnmPEVLSolver(this, restriction, false, active).iterator();
                this.afsEnumerator = new MemoryAbortableIterable<Pair<Map<FunctionSymbol, YNM[]>, Set<? extends GeneralizedRule>>>(iterator);
                this.afsEnumeratorRestriction = restriction < 0 ? -1 : restriction;
            }
            return this.afsEnumerator;
        }
    }

    /**
     * forget the AFS iterable to be able to free the memory
     */
    public void forgetAfsIterable() {
        synchronized(this.afsLock) {
            this.afsEnumerator = null;
        }
    }

    /**
     * @return Maximal arity of signature
     */
    public int getMaxArity() {
        if(this.maxArity == null) {
            int max =0;
            for(final FunctionSymbol fs : CollectionUtils.getFunctionSymbols(this.P)) {
                final int arity = fs.getArity();
                if (arity > max) {
                    max = arity;
                }
            }
            final int maxArityOfRAndQ = this.getRwithQ().getMaxArity();
            if(max > maxArityOfRAndQ) {
                this.maxArity = max;
            }
            else {
                this.maxArity = maxArityOfRAndQ;
            }
        }
        return this.maxArity;
    }

    public ImmutableSet<Rule> getP() {
        return this.P;
    }

    public boolean QsupersetOfLhsR() {
        return this.rWithQ.QsupersetOfLhsR();
    }

    public boolean getMinimal() {
        return this.minimal;
    }

    public boolean getInnermost() {
        return this.rWithQ.QsupersetOfLhsR();
    }

    public QTRSProblem getRwithQ() {
        return this.rWithQ;
    }

    public ImmutableSet<Rule> getR() {
        return this.rWithQ.getR();
    }

    public QTermSet getQ() {
        return this.rWithQ.getQ();
    }

    /**
     * return an identical pair to the input.
     * if this input already occurs as pair, then this is returned
     * (so, the variable names of the already present pair are taken)
     * @param pair
     * @return
     */
    public Rule getPair(final Rule pair) {
        if (this.getP().contains(pair)) {
            for (final Rule origPair : this.getP()) {
                if (origPair.equals(pair)) {
                    return origPair;
                }
            }
        }
        return pair;
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

        final QDPProblem other = (QDPProblem) oth;

        if (this.minimal != other.minimal) {
            return false;
        }

        if (!this.P.equals(other.P)) {
            return false;
        }

        return this.rWithQ.equals(other.rWithQ);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder s = new StringBuilder();
        s.append(o.export("Q DP problem:"));
        s.append(o.cond_linebreak());
        if (this.P.isEmpty()) {
            s.append("P is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS P consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.P, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        if (this.getR().isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.getR(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        if (this.getQ().getTerms().isEmpty()) {
            s.append("Q is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The set Q consists of the following terms:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.getQ().getTerms(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        s.append(o.export("We have to consider all "+(this.minimal ? "minimal " : "")+"(P,Q,R)-chains."));
        return s.toString();
    }

    /**
     * Output as WST-like traditional DP.
     * <P>
     * <b>Note:</b> This is not complete as Q is lost!
     */
    public String toWSTDP() {
        final StringBuilder s = new StringBuilder();
        final Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>();
        s.append("(PAIRS\n");
        for (final Rule pair : this.P) {
            vars.addAll(pair.getVariables());
            s.append("  "+pair.toString()+"\n");
        }
        s.append(")\n");
        s.append("(RULES\n");
        for (final Rule rule : this.rWithQ.getR()) {
            vars.addAll(rule.getVariables());
            s.append("  "+rule.toString()+"\n");
        }
        s.append(")\n");
        s.append("(VAR");
        for (final TRSVariable var : vars) {
            s.append(" "+var.toString());
        }
        s.append(")\n");
        if (this.getInnermost()) {
            s.append("(STRATEGY INNERMOST)\n");
        }
        return s.toString();
    }

    @Override
    public String externName() {
        return "qdp";
    }

    /**
     * Output as AProVE QDP, with set of terms Q, minimal flag and dependency
     * graph.
     */
    @Override
    public String toExternString() {
        final StringBuilder s = new StringBuilder();
        final Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>();
        for (final Rule pair : this.P) {
            vars.addAll(pair.getVariables());
        }
        for (final Rule rule : this.rWithQ.getR()) {
            vars.addAll(rule.getVariables());
        }
        for (final TRSFunctionApplication funcApp : this.getQ().getTerms()) {
            vars.addAll(funcApp.getVariables());
        }
        final Set<String> varNames = new LinkedHashSet<String>();
        for(final TRSVariable x : vars) {
            varNames.add(x.getName());
        }
        final Set<String> signatureNames = new LinkedHashSet<String>();
        for(final FunctionSymbol f : this.getSignature()) {
            signatureNames.add(f.getName());
        }

        final FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.VARIABLES);
        fng.lockNames(signatureNames);
        fng.lockNames(varNames);

        final Set<String> collisions = new HashSet<String>(varNames);
        collisions.retainAll(signatureNames);

        final Map<TRSVariable, TRSVariable> varMap =
            new LinkedHashMap<TRSVariable, TRSVariable>();
        for (final TRSVariable x : vars) {
            if (collisions.contains(x.toString())) {
                varMap.put(x, TRSTerm.createVariable(fng.getFreshName(
                    x.toString(), false)));
            } else {
                varMap.put(x, x);
            }
        }
        final TRSSubstitution subst =
            TRSSubstitution.create(ImmutableCreator.create(varMap));

        // output
        s.append("(VAR");
        for (final TRSVariable var : varMap.values()) {
            s.append(" " + var.toString());
        }
        s.append(")\n");
        int currentVertex = 1;
        final Map<Rule, Integer> vertexNumbers = new HashMap<Rule, Integer>();
        s.append("(PAIRS\n");
        for (Rule pair : this.P) {
            pair = pair.applySubstitution(subst);
            vertexNumbers.put(pair, currentVertex);
            ++currentVertex;
            s.append("  " + pair.toString() + "\n");
        }
        s.append(")\n");
        s.append("(RULES\n");
        for (Rule rule : this.rWithQ.getR()) {
            rule = rule.applySubstitution(subst);
            s.append("  " + rule.toString() + "\n");
        }
        s.append(")\n");
        s.append("(Q\n");
        for (TRSFunctionApplication funcApp : this.getQ().getTerms()) {
            funcApp = funcApp.applySubstitution(subst);
            s.append("  ");
            s.append(funcApp.toString());
            s.append("\n");
            vars.addAll(funcApp.getVariables());
        }
        s.append(")\n");
        s.append("(EDGES\n");
        for (final Edge<?, Rule> node : this.getDependencyGraph().getGraph().getEdges()) {
            final Integer from = vertexNumbers.get(node.getStartNode().getObject());
            final Integer to = vertexNumbers.get(node.getEndNode().getObject());
            s.append("    ");
            s.append(from);
            s.append(" -> ");
            s.append(to);
            s.append("\n");
        }
        s.append(")\n");
        if (this.getMinimal()) {
            s.append("(MINIMAL)\n");
        } else {
            s.append("(NOT MINIMAL)\n");
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
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element e = XMLTag.QDP_OBL.createElement(doc);
        final Element f = XMLTag.QDP.createElement(doc);

        final Element dps = XMLTag.DPS.createElement(doc);
        final Graph<Rule,?> graph = this.graph.getGraph();
        for (final Node<Rule> dp : graph.getNodes()) {
            final Element rule = dp.getObject().toDOM(doc, xmlMetaData);
            XMLAttribute.RULE_IDENTIFIER.setAttribute(rule, dp.getNodeNumber()+"");
            dps.appendChild(rule);
        }

        for (final Edge<?,Rule> edge : graph.getEdges()) {
            final Element edg = XMLTag.DP_EDGE.createElement(doc);
            XMLAttribute.DP_EDGE_FROM.setAttribute(edg, edge.getStartNode().getNodeNumber()+"");
            XMLAttribute.DP_EDGE_TO.setAttribute(edg, edge.getEndNode().getNodeNumber()+"");
            dps.appendChild(edg);
        }

        f.appendChild(dps);

        final Element trs = XMLTag.TRS.createElement(doc);
        CollectionUtils.addChildren(this.getR(), trs, doc, xmlMetaData);
        f.appendChild(trs);

        f.appendChild(this.getQ().toDOM(doc, xmlMetaData));

        final Element innermost = XMLTag.INNERMOST.createElement(doc);

        if (!this.rWithQ.QsupersetOfLhsR()) {
            if (this.rWithQ.isExactlyInnermost()) {
                XMLAttribute.EXACTLY_INNERMOST.setAttribute(innermost, "true");
                f.appendChild(innermost);
            }
        } else {
            XMLAttribute.EXACTLY_INNERMOST.setAttribute(innermost, "false");
            f.appendChild(innermost);
        }

        final Element min = XMLTag.MINIMALITY.createElement(doc);
        min.appendChild(XMLTag.createBoolean(doc, this.minimal));
        f.appendChild(min);

        final Element sig = XMLTag.SIGNATURE.createElement(doc);
        CollectionUtils.addChildren(this.getSignature(), sig, doc, xmlMetaData);
        f.appendChild(sig);

        e.appendChild(f);
        return e;
    }

    @Override
    public Element getCPFInput(final Document doc, final XMLMetaData xmlMetaData, final TruthValue tv) {
        final Element dpInput = CPFTag.DP_INPUT.createElement(doc);

        final Element trs = CPFTag.TRS.createElement(doc);
        final Element rules1 = CPFTag.RULES.createElement(doc);
        for (final Rule r : this.getR()) {
            rules1.appendChild(r.toCPF(doc, xmlMetaData));
        }
        trs.appendChild(rules1);
        dpInput.appendChild(trs);

        final Element dps = CPFTag.DPS.createElement(doc);
        final Element rules2 = CPFTag.RULES.createElement(doc);
        final Graph<Rule, ?> graph = this.graph.getGraph();
        for (final Node<Rule> dp : graph.getNodes()) {
            final Element rule = dp.getObject().toCPF(doc, xmlMetaData);
            rules2.appendChild(rule);
        }
        dps.appendChild(rules2);
        dpInput.appendChild(dps);

        final Element strategy = CPFTag.STRATEGY.createElement(doc);
        if (!this.rWithQ.QsupersetOfLhsR()) {
            if (this.rWithQ.isExactlyInnermost()) {
                strategy.appendChild(CPFTag.INNERMOST.createElement(doc));
                dpInput.appendChild(strategy);
            }
        } else {
            strategy.appendChild(this.getQ().toCPF(doc, xmlMetaData));
            dpInput.appendChild(strategy);
        }

        final Element minimal = CPFTag.MINIMAL.createElement(doc);
        minimal.appendChild(doc.createTextNode("" + this.minimal));
        dpInput.appendChild(minimal);

        return dpInput;
    }

    @Override
    public Element getCPFAssumption(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final CPFModus modus,
        final TruthValue tv)
    {
        if (modus.isPositive()) {
            return CPFTag.DP_PROOF.create(
                doc,
                CPFTag.FINITENESS_ASSUMPTION.create(doc, this.getCPFInput(doc, xmlMetaData, tv)));
        } else {
            return CPFTag.DP_NONTERMINATION_PROOF.create(
                doc,
                CPFTag.INFINITENESS_ASSUMPTION.create(doc, this.getCPFInput(doc, xmlMetaData, tv)));
        }
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new QDPProofPurposeDescriptor(this);
    }

    @Override
    public String toDOT() {
        return this.graph.toDOT();
    }

    @Override
    public BasicObligation maybeCopy() {
        // Share the obligation but create a new graph instance
        return new QDPProblem(this.rWithQ.maybeCopy(), QDependencyGraph.create(this.graph.getGraph(), this.rWithQ), this.minimal, this.isRRRQreducable, this.constraintsCache);
    }

    @Override
    public FeatureVector<Features> getFeatureVector() {
        return FeaturesQDP.getFeatures(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "qdp";
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.BasicObligation.DefaultBasicObligation#offersCertifiableTechniques()
     */
    @Override
    public boolean offersCertifiableTechniques() {
        return true;
    }

}
