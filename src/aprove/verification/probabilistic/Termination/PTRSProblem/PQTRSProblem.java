package aprove.verification.probabilistic.Termination.PTRSProblem;

import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.*;
import aprove.verification.probabilistic.Termination.ADPProblem.AST.*;
import aprove.verification.probabilistic.Termination.ADPProblem.SAST.*;
import immutables.*;

/**
 * @author J-C Kassing
 * @version $Id$
 */
public class PQTRSProblem extends DefaultBasicObligation implements Immutable {

    // ================================================================================
    // Properties
    // ================================================================================

    private final ProbabilisticTerminationResult target;
    private final QRewriteStrategy strat;
    private final boolean basic;

    private final Set<ProbabilisticRule> PR;
    private final QTermSet Q;

    /* Computed Values */
    private final boolean QsuperR;
    private volatile CriticalPairs critPairs;
    private final ImmutableSet<FunctionSymbol> signature;
    private volatile ImmutableSet<FunctionSymbol> defSymbolsOfR;
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<ProbabilisticRule>> ruleMap;

    // a map from symbols of rhs to rules (which have to read from right to left!),
    // collapsing rules can be found with the null-functionSymbol
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> reverseRuleMap;

    private volatile ProbQUsableRules qUsableRules = null;

    private final int hashCode;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    /**
     * creates a PQTRS problem.
     * @param R - the PTRS
     * @param Q - the lhs's of Q where every term is in standard numbering
     * @param strat - the rewrite strategy that we want to analyze
     */
    public PQTRSProblem(final Set<ProbabilisticRule> probabilisticRules,
        final QTermSet Q,
        final QRewriteStrategy strat,
        final ProbabilisticTerminationResult target,
        final boolean basic) {
        super("PQTRS", "Probabilistic QTRS");

        this.PR = probabilisticRules;
        this.strat = strat;
        this.target = target;
        this.basic = basic;
        this.Q = Q;
        this.QsuperR = this.Q.canAllLhsBeRewritten(this.PR);
        this.critPairs = null;
        this.defSymbolsOfR = null;
        this.ruleMap = null;
        final Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.PR);
        this.signature = ImmutableCreator.create(signature);
        this.hashCode = Objects.hash(this.PR) + Objects.hash(Q);

        calculateDefSymbolsAndRuleMap();
    }

    /**
     * creates a PQTRS problem.
     * @param R - the PTRS
     * @param Q - the lhs's of Q where every term is in standard numbering
     * @param QsuperR - the flag whether Q is a superset of the LHSs of R.
     * @param isRRRQreducable - a cached value whether some lhs of R is Q-reducable below the root
     */
    private PQTRSProblem(final ImmutableSet<ProbabilisticRule> probabilisticRules,
        final QTermSet Q,
        final boolean QsuperR,
        final ProbQUsableRules qUsableRules,
        final QRewriteStrategy strat,
        final ProbabilisticTerminationResult target,
        final boolean basic) {
        super("PTRS", "Probabilistic TRS");

        this.PR = probabilisticRules;
        this.strat = strat;
        this.target = target;
        this.basic = basic;
        this.Q = Q;

        this.QsuperR = QsuperR;
        this.qUsableRules = qUsableRules;

        this.critPairs = null;
        this.defSymbolsOfR = null;
        this.ruleMap = null;
        final Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.PR);
        this.signature = ImmutableCreator.create(signature);
        this.hashCode = Objects.hash(this.PR) + Objects.hash(Q);

        calculateDefSymbolsAndRuleMap();
    }

    /**
     * creates a new PTRS-Problem for the given collection of Rules,
     * Q will be empty
     * @param R
     */
    public static PQTRSProblem create(final ImmutableSet<ProbabilisticRule> PR,
        final QRewriteStrategy strat,
        final ProbabilisticTerminationResult target,
        final boolean basic) {
        return PQTRSProblem.create(PR, new QTermSet(new ArrayList<>(0)), strat, target, basic);
    }

    /**
     * creates a new PTRS-Problem for the given collection of Rules for R and Q
     * @param R
     * @param Q_it
     */
    public static PQTRSProblem create(final ImmutableSet<ProbabilisticRule> PR,
        final Iterable<TRSFunctionApplication> Q_it,
        final QRewriteStrategy strat,
        final ProbabilisticTerminationResult target,
        final boolean basic) {
        return PQTRSProblem.create(PR, new QTermSet(Q_it), strat, target, basic);
    }

    /**
     * creates a new PTRS-Problem for the given collection of Rules for R and Q
     * @param R_it
     * @param Q
     */
    public static PQTRSProblem create(final ImmutableSet<ProbabilisticRule> PR,
        final QTermSet Q,
        final QRewriteStrategy strat,
        final ProbabilisticTerminationResult target,
        final boolean basic) {
        return new PQTRSProblem(PR, Q, strat, target, basic);
    }

    // ================================================================================
    // Accessors
    // ================================================================================

    public Set<ProbabilisticRule> getProbabilisticRules() {
        return this.PR;
    }

    public Set<ProbabilisticRule> getPR() {
        return this.PR;
    }

    public ProbabilisticTerminationResult getTarget() {
        return this.target;
    }

    public QRewriteStrategy getStrat() {
        return this.strat;
    }

    public boolean isBasic() {
        return this.basic;
    }

    public ImmutableSet<FunctionSymbol> getSignature() {
        return this.signature;
    }

    public ImmutableSet<FunctionSymbol> getDefSymbolsOfR() {
        return this.defSymbolsOfR;
    }

    public ImmutableMap<FunctionSymbol, ImmutableSet<ProbabilisticRule>> getRuleMap() {
        return this.ruleMap;
    }

    public Set<TRSVariable> getVariables() {
        final Set<TRSVariable> res = new HashSet<>();
        for (final ProbabilisticRule rule : getPR()) {
            res.addAll(rule.getLeft().getVariables());
            for (final TRSTerm term : rule.getRight().getSupport()) {
                res.addAll(term.getVariables());
            }
        }
        return res;
    }

    public Pair<Set<ProbabilisticRule>, Map<FunctionSymbol, FunctionSymbol>> getProbabilisticDPs() {
        final Set<ProbabilisticRule> dps = new LinkedHashSet<>();
        final Set<FunctionSymbol> signature = new LinkedHashSet<>(getSignature());
        final Set<FunctionSymbol> defs = getDefSymbolsOfR();
        final Map<FunctionSymbol, FunctionSymbol> annoMap = new LinkedHashMap<>();

        for (final FunctionSymbol fs : defs) {
            QTRSProblem.getTupleSymbol(fs, annoMap, signature);
        }

        for (final ProbabilisticRule pr : this.PR) {

            final TRSFunctionApplication lhs = pr.getLeft();
            final MultiDistribution<TRSTerm> rhs = pr.getRight();

            final HashMultiSet<Pair<TRSTerm, BigFraction>> resRhs = new HashMultiSet<>();

            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rhs.getProbabilityMapping().entrySet()) {
                final TRSTerm term = entry.getKey().getKey();
                final BigFraction prob = entry.getKey().getValue();
                final Integer amount = entry.getValue();

                final TRSTerm annotatedTerm = term.replaceAllFunctionSymbols(annoMap);
                final Pair<TRSTerm, BigFraction> elementAndProbPair = new Pair<>(annotatedTerm, prob);
                for (int i = 0; i < amount; i++) {
                    resRhs.add(elementAndProbPair);
                }
            }
            final FunctionSymbol tf = QTRSProblem.getTupleSymbol(lhs.getRootSymbol(), annoMap, signature);
            final TRSFunctionApplication tlhs = TRSTerm.createFunctionApplication(tf, lhs.getArguments());

            final MultiDistribution<TRSTerm> rightHandDist = MultiDistribution.create(resRhs);
            dps.add(ProbabilisticRule.create(tlhs, rightHandDist));
        }
        return new Pair<>(dps, annoMap);
    }

    /** Returns true, if this PTRS is a normal PTRS, i.e. every probabilistic rules has the form l -> {1:r}. */
    public boolean isNonProbabilistic() {
        for (final ProbabilisticRule pr : this.PR) {
            if (!pr.isDeterministic()) {
                return false;
            }
        }
        return true;
    }

    /**
     * returns whether R has at least one collapsing rule
     * @return
     */
    public boolean isCollapsing() {
        return getReverseRuleMap().containsKey(null);
    }

    /**
     * returns whether R contains at least one duplicating rule
     * @return
     */
    public boolean isDuplicating() {
        for (final ProbabilisticRule rule : getPR()) {
            if (rule.isDuplicating()) {
                return true;
            }
        }
        return false;
    }

    /**
     * returns whether R contains at least one variable occurrence decreasing rule
     * @return
     */
    public boolean isVariableOccDecreasing() {
        for (final ProbabilisticRule rule : getPR()) {
            if (rule.isVariableOccDecreasing()) {
                return true;
            }
        }
        return false;
    }

    /**
     * returns whether all rules in R are left linear
     * @return
     */
    public boolean isLeftLinear() {
        for (final ProbabilisticRule rule : getPR()) {
            if (!rule.isLeftLinear()) {
                return false;
            }
        }
        return true;
    }

    /**
     * get R^{-1} as a mapping from function symbols of rhs to corresponding rules.
     * Note that the rules a still from left to right, i.e. one has to read the rules
     * reversed!
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> getReverseRuleMap() {
        if (this.reverseRuleMap == null) {
            synchronized (this) {
                if (this.reverseRuleMap == null) {
                    calculateReverseRuleMap();
                }
            }
        }
        return this.reverseRuleMap;
    }

    public ProbQUsableRules getProbQUsableRulesCalculator(final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        if (this.qUsableRules == null) {
            synchronized (this) {
                if (this.qUsableRules == null) {
                    this.qUsableRules = new ProbQUsableRules(this, annoMap);
                }
            }
        }
        return this.qUsableRules;
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
     * Therefore, if the PTRS terminates with the innermost rewrite relation,
     * it also terminates with the Q rewrite relation.
     */
    public boolean QsupersetOfLhsR() {
        return this.QsuperR;
    }

    /**
     * creates a sub problem where the new R are the usable rules of the given
     * DP problem qdp. The qdp must be innermost!
     * @param adpp
     */
    public PQTRSProblem createUsableRulesSubProblem(final ADP_AST_Problem adpp) {
        final ImmutableSet<ProbabilisticRule> usableRules = adpp.getUsableRules();
        if (this.PR.size() == usableRules.size()) {
            if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                System.err.println("Warning: createUsableRulesSubProblem in QTRS produces identity");
            }
            return this;
        }
        final boolean qSuperR = true;
        return new PQTRSProblem(usableRules,
            this.Q,
            qSuperR,
            getProbQUsableRulesCalculator(adpp.getBiAnnoMap()),
            adpp.getStrat(),
            ProbabilisticTerminationResult.AST,
            adpp.isBasic());
    }

    /**
     * creates a sub problem where the new R are the usable rules of the given
     * DP problem qdp. The qdp must be innermost!
     * @param adpp
     */
    public PQTRSProblem createUsableRulesSubProblem(final ADP_SAST_Problem adpp) {
        final ImmutableSet<ProbabilisticRule> usableRules = adpp.getUsableRules();
        if (this.PR.size() == usableRules.size()) {
            if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                System.err.println("Warning: createUsableRulesSubProblem in QTRS produces identity");
            }
            return this;
        }
        final boolean qSuperR = true;
        return new PQTRSProblem(usableRules,
            this.Q,
            qSuperR,
            getProbQUsableRulesCalculator(adpp.getBiAnnoMap()),
            adpp.getStrat(),
            ProbabilisticTerminationResult.AST,
            adpp.isBasic());
    }

    /**
     * creates a sub problem where the new R are the usable rules of the given
     * DP problem qdp. The qdp must be basic!
     * @param adpp
     */
    public PQTRSProblem createBasicUsableRulesSubProblem(final ADP_AST_Problem adpp) {
        final ImmutableSet<ProbabilisticRule> basicUsableRules = adpp.getBasicUsableRules();
        if (this.PR.size() == basicUsableRules.size()) {
            if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                System.err.println("Warning: createUsableRulesSubProblem in QTRS produces identity");
            }
            return this;
        }
        final boolean qSuperR = true;
        return new PQTRSProblem(basicUsableRules,
            this.Q,
            qSuperR,
            getProbQUsableRulesCalculator(adpp.getBiAnnoMap()),
            adpp.getStrat(),
            ProbabilisticTerminationResult.AST,
            adpp.isBasic());
    }

    /**
     * creates a sub problem where the new R are the usable rules of the given
     * DP problem qdp. The qdp must be innermost!
     * @param adpp
     */
    public PQTRSProblem createBasicUsableRulesSubProblem(final ADP_SAST_Problem adpp) {
        final ImmutableSet<ProbabilisticRule> basicUsableRules = adpp.getBasicUsableRules();
        if (this.PR.size() == basicUsableRules.size()) {
            if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                System.err.println("Warning: createUsableRulesSubProblem in QTRS produces identity");
            }
            return this;
        }
        final boolean qSuperR = true;
        return new PQTRSProblem(basicUsableRules,
            this.Q,
            qSuperR,
            getProbQUsableRulesCalculator(adpp.getBiAnnoMap()),
            adpp.getStrat(),
            ProbabilisticTerminationResult.SAST,
            adpp.isBasic());
    }

    /**
     * creates a sub problem with less rules in R
     * @param rules
     * @return Sub problem with less rules and the same strat and same probabilistic termination target
     */
    public PQTRSProblem createSubProblem(final ImmutableSet<ProbabilisticRule> rules) {
        if (Globals.useAssertions) {
            assert (this.PR.containsAll(rules));
        }
        return new PQTRSProblem(rules, this.Q, this.strat, this.target, this.basic);
    }

    /**
     * creates a Probabilistic QTRS from this one with different Q
     * @param Q
     * @return New problem with same rules but new Q and the same strat and same probabilistic termination target
     */
    public PQTRSProblem create(final QTermSet Q) {
        if (Q.getTerms().equals(this.Q.getTerms())) {
            return this;
        }
        return new PQTRSProblem(getPR(), Q, this.strat, this.target, this.basic);
    }

    //TODO Create correct critical pairs if needed one day and remove this hack.
    /**
     * Returns the non-probabilistic l-abstraction np_l(S) of this PTRS.
     * This is the same as np(S) but for each rule l -> {p_1:r_1, ..., p_k:r_k}
     * we create only one rule l -> r_1.
     * (used to check for critical pairs but not to compute them!)
     * Ignores the rewrite strategy and creates an empty set Q.
     * @return
     */
    public QTRSProblem getNonProbLAbstraction() {
        // first copy the original signature
        final FunctionSymbolGenerator funSymGen = new FunctionSymbolGenerator(this.signature.size() + this.PR.size());

        for (final FunctionSymbol f : this.signature) {
            final FunctionSymbol g = funSymGen.getFresh(f.getName(),
                f
                    .getArity());
            if (Globals.useAssertions) {
                assert (f.equals(g));
            }
        }
        final HashSet<Rule> allNonProbLRules = new HashSet<>();
        for (final ProbabilisticRule pr : this.PR) {
            final FunctionSymbol g = funSymGen.getFresh("fresh", 0);
            allNonProbLRules.add(Rule.create(pr.getLeft(), TRSTerm.createFunctionApplication(g)));
        }
        return QTRSProblem.create(ImmutableCreator.create(allNonProbLRules));
    }

    /**
     * Returns the non-probabilistic abstraction np(S) of this PTRS.
     * For each rule l -> {p_1:r_1, ..., p_k:r_k}
     * we create k new rules l -> r_j.
     *
     * Ignores the rewrite strategy and creates an empty set Q.
     * @return
     */
    public QTRSProblem getNonProbAbstraction() {
        final Set<Rule> nonPropRules = new HashSet<>();
        for (final ProbabilisticRule pr : this.PR) {
            for (final TRSTerm r : pr.getRight().getSupport()) {
                nonPropRules.add(Rule.create(pr.getLeft(), r));
            }
        }
        return QTRSProblem.create(ImmutableCreator.create(nonPropRules), this.Q);
    }

    //TODO Fix this.
    /**
     * CURRENTLY ONLY BE USABLE TO CHECK IF CriticalPairs ARE EMPTY!
     * THE RESULTING CriticalPairs ARE NOT CONTAINING EVERYTHING THEY SHOULD!
     *
     * @return The set of critical pairs for this PQTRS
     */
    public CriticalPairs getCriticalPairs() {
        if (this.critPairs == null) {
            synchronized (this) {
                if (this.critPairs == null) {
                    this.critPairs = new CriticalPairs(getNonProbLAbstraction());
                }
            }
        }
        return this.critPairs;
    }

    // ================================================================================
    // Internals
    // ================================================================================

    private void calculateDefSymbolsAndRuleMap() {
        final Map<FunctionSymbol, Set<ProbabilisticRule>> ruleMap = new LinkedHashMap<>();
        for (final ProbabilisticRule rule : this.PR) {
            final FunctionSymbol f = rule.getRootSymbol();
            Set<ProbabilisticRule> fRules = ruleMap.get(f);
            if (fRules == null) {
                fRules = new LinkedHashSet<>();
                ruleMap.put(f, fRules);
            }
            fRules.add(rule);
        }
        // make immutable
        final Map<FunctionSymbol, ImmutableSet<ProbabilisticRule>> immutableMap = new LinkedHashMap<>();
        for (final Map.Entry<FunctionSymbol, Set<ProbabilisticRule>> entry : ruleMap.entrySet()) {
            immutableMap.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }
        this.ruleMap = ImmutableCreator.create(immutableMap);
        this.defSymbolsOfR = ImmutableCreator.create(immutableMap.keySet());
    }

    private void calculateReverseRuleMap() {
        final Map<FunctionSymbol, Set<Rule>> reverseRuleMap = ProbabilisticRule.getReversedRuleMap(this.PR);
        final Map<FunctionSymbol, ImmutableSet<Rule>> immutableMap = new LinkedHashMap<>();
        for (final Map.Entry<FunctionSymbol, Set<Rule>> entry : reverseRuleMap.entrySet()) {
            immutableMap.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }
        this.reverseRuleMap = ImmutableCreator.create(immutableMap);
    }

    /**
     * very simple fresh name generator
     */
    private static final class FunctionSymbolGenerator {

        private final Set<FunctionSymbol> fs;

        public FunctionSymbolGenerator(final int size) {
            this.fs = new HashSet<>(size);
        }

        public FunctionSymbol getFresh(final String name, final int arity) {
            int j = 0;
            String currentName = name;
            FunctionSymbol f;
            while (true) {
                f = FunctionSymbol.create(currentName, arity);
                if (this.fs.add(f)) {
                    return f;
                } else {
                    currentName = name + j;
                    j++;
                }
            }
        }

    }

    // ================================================================================
    // Utility
    // ================================================================================

    @Override
    public String getStrategyName() {
        return switch (this.target) {
            case certainTermination -> switch (this.strat) {
                                case Q_FULL -> "pqtrs_TERM";
                                case Q_PARALLEL_SIMULTANEOUS -> "pqtrs_ps_TERM";
                                default -> "pqtrs_TERM";
                            };
            case AST -> switch (this.strat) {
                                case Q_FULL -> "pqtrs_AST";
                                case Q_PARALLEL_SIMULTANEOUS -> "pqtrs_ps_AST";
                                default -> "pqtrs_AST";
                            };
            case SAST -> switch (this.strat) {
                                case Q_FULL -> "pqtrs_SAST";
                                case Q_PARALLEL_SIMULTANEOUS -> "pqtrs_ps_SAST";
                                default -> "pqtrs_SAST";
                            };
            default -> "pqtrs_TERM";
        };
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "AST");
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder s = new StringBuilder();
        s.append(eu.export("Probabilistic Q term rewrite system:"));
        s.append(eu.cond_linebreak());
        s.append(eu.export("The PQTRS has the following probabilistic rules:"));
        s.append(eu.cond_linebreak());
        s.append(eu.set(this.PR, Export_Util.RULES));
        s.append(eu.cond_linebreak());
        s.append(eu.export("And Q contains the following terms:"));
        s.append(eu.cond_linebreak());
        s.append(eu.set(this.Q.getTerms(), Export_Util.NICE_SET));
        s.append(eu.cond_linebreak());

        return s.toString();
    }

    @Override
    public String toString() {
        return export(new PLAIN_Util());
    }

    @Override
    public boolean equals(final Object oth) {
        if (this == oth) {
            return true;
        }
        if (oth == null || oth.getClass() != this.getClass()) {
            return false;
        }
        final PQTRSProblem other = (PQTRSProblem) oth;
        if (!this.PR.equals(other.PR)) {
            return false;
        }

        return this.Q.equals(other.Q);
    }
}
