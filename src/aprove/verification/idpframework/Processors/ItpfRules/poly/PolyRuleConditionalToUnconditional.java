package aprove.verification.idpframework.Processors.ItpfRules.poly;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Core.Utility.PrimeNumbers.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.ItpfRules.ItpfAtomReplaceData.*;
import aprove.verification.idpframework.Processors.ItpfRules.poly.PolyRuleConditionalToUnconditional.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;
/**
 *
 * @author MP
 */
public class PolyRuleConditionalToUnconditional<C extends SemiRing<C>> extends AbstractItpfReplaceRule.ItpfReplaceRuleSkeleton<PreconditionCache, Unused> {

    public static enum SearchMode {
        FULL, P_LEQ_Q, P_EQ_Q, P_Q_ONE
    }

    private static final BigInt PRIME_FACTORIZATION_BOUND = BigInt.create(BigInteger.valueOf(2000));

    private final SearchMode searchMode = SearchMode.FULL;
    private final boolean usePrimeFactorization = true;

    public PolyRuleConditionalToUnconditional() {
        super(new ExportableString("PolyRuleConditionalToUnconditional"), new ExportableString("PolyRuleConditionalToUnconditional"));
    }

    @Override
    public boolean isApplicable(final IDPProblem idp) {
        return idp.getIdpGraph().getPolyInterpretation() != null && idp.getIdpGraph().getPolyInterpretation().getRing().isSameRing(BigInt.ZERO);
    }

    @Override
    public boolean isApplicable(final IDPProblem idp,
        final Itpf formula,
        final ApplicationMode mode) {
        return this.isApplicable(idp);
    }

    @Override
    public boolean isComplete() {
        return true;
    }

    @Override
    public boolean isSound() {
        return false;
    }

    @Override
    public Collection<? extends Mark<?>> getUsedMarks() {
        return Collections.<Mark<?>>singleton(this);
    }

    @Override
    public boolean isAtomicMark() {
        return false;
    }

    @Override
    public boolean isClauseMark() {
        return true;
    }

    @Override
    public boolean isContextFree() {
        return true;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return this.equals(mark);
    }

    @Override
    protected PreconditionCache createContext(final IDPProblem idp,
        final ItpfAndWrapper precondition,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        return new PreconditionCache();
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final PreconditionCache context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException {
        if (atom.isPoly() && positive && !executionRequirements.isSound()) {
            @SuppressWarnings("unchecked")
            final ItpfPolyAtom<BigInt> polyAtom = (ItpfPolyAtom<BigInt>) atom;
            final PolyInterpretation<BigInt> polyInterpretation = polyAtom.getInterpretation();

            final List<ItpfAtomReplaceData> replaceDatas = new ArrayList<ItpfAtomReplaceData>();

            for (final ItpfConjClause preconditionClause : precondition.getFormula().getClauses()) {
                final Conjunction<Polynomial<BigInt>> polynomialPrecondition = this.getPolynomialPreconditions(preconditionClause, context, polyInterpretation);

                final Pair<Set<ItpfPolyAtom<BigInt>>, ItpfPolyAtom<BigInt>> newPolyLiteral = PolyRuleConditionalToUnconditional.processPolyConclusion(
                    polynomialPrecondition,
                    polyAtom,
                    polyInterpretation,
                    this.searchMode,
                    this.usePrimeFactorization,
                    aborter);

                final LiteralMap newLiterals = new LiteralMap();
                newLiterals.putAll(newPolyLiteral.x, true);
                if (newPolyLiteral.y != null) {
                    newLiterals.put(newPolyLiteral.y, true);
                }

                replaceDatas.add(
                    new LiteralMapData(
                        newLiterals,
                        ITerm.EMPTY_SET));
            }

            return this.createReplaceData(ItpfFactory.EMPTY_QUANTORS, ImmutableCreator.create(replaceDatas), ImplicationType.COMPLETE, ApplicationMode.SingleStep, false);

        }
        return null;
    }

    private Conjunction<Polynomial<BigInt>> getPolynomialPreconditions(final ItpfConjClause preconditionClause,
        final PreconditionCache context, final PolyInterpretation<BigInt> polyInterpretation) {
        Conjunction<Polynomial<BigInt>> result = context.get(preconditionClause);
        if (result == null) {
            result = PolyRuleConditionalToUnconditional.getPolynomialPreconditions(preconditionClause, polyInterpretation);
            context.put(preconditionClause, result);
        }
        return result;
    }

    public static Conjunction<Polynomial<BigInt>> getPolynomialPreconditions(final ItpfConjClause precondition,
        final PolyInterpretation<BigInt> polyInterpretation) {

        final ArrayList<Polynomial<BigInt>> preconditions = new ArrayList<Polynomial<BigInt>>(precondition.getLiterals().size());

        for (final Map.Entry<? extends ItpfAtom, Boolean> literal : precondition.getLiterals().entrySet()) {
            if (literal.getKey().isPoly() && literal.getValue().booleanValue()) {
                final ItpfPolyAtom<BigInt> polyAtom = (ItpfPolyAtom<BigInt>) literal.getKey();
                if (polyAtom.getConstraintType() == ConstraintType.GT) {
                    preconditions.add(polyAtom.getPoly().subtract(polyAtom.getPoly().one()));
                } else {
                    preconditions.add(polyAtom.getPoly());
                }
            }
        }

        return new Conjunction<Polynomial<BigInt>>(ImmutableCreator.create(preconditions));
    }

    /**
     * We can transform
     *   p_1 >= q_1 /\ ... /\ p_n >= q_n  =>  r >= s
     * to
     *   P[r] - P[s]  >=  Q[p_1, ..., p_n] - Q[q_1, ..., q_n]
     * where P is an arbitrary  weakly  monotonic polynomial
     *   and Q is an arbitrary strictly monotonic polynomial.
     *
     * TODO generalize shape of these polynomials
     *
     * If the result of the transformation is satisfiable, then also the
     * original conditional constraint is.
     *
     * @param conclusionAtom - an ItpfPolyAtom of the conclusion (r >= 0)
     * @return new conclusion atoms whose satisfiability entails satisfiability of the
     *  corresponding conditional constraint with conds as conditions and
     *  constraint as constraint that must hold whenever all of conditions
     *  hold
     * @throws AbortionException
     */
    public static Pair<Set<ItpfPolyAtom<BigInt>>, ItpfPolyAtom<BigInt>> processPolyConclusion(
        final Conjunction<Polynomial<BigInt>> polynomialPrecondition,
        final ItpfPolyAtom<BigInt> conclusionPolyAtom,
        final PolyInterpretation<BigInt> polyInterpretation,
        final SearchMode searchMode,
        final boolean usePrimeFactorization,
        final Abortion aborter) throws AbortionException {

        final BigInt ring = BigInt.ZERO;

        // P[r] - P[s]  >=  Q[p_1, ..., p_n] - Q[q_1, ..., q_n]
        //   is equivalent to
        // P[r] - P[s] - Q[p_1, ..., p_n] + Q[q_1, ..., q_n]  >=  0.

        final PolyFactory polyFactory = polyInterpretation.getFactory();


        final Set<ItpfPolyAtom<BigInt>> sideConstraints = new LinkedHashSet<ItpfPolyAtom<BigInt>>();

        Polynomial<BigInt> current;
        Polynomial<BigInt> pCoeffPoly;
        if (polynomialPrecondition.size() > 1 && searchMode != SearchMode.P_Q_ONE && searchMode != SearchMode.P_EQ_Q) {
            final SemiRingDomain<BigInt> pVarRange = DomainFactory.createVarRange(BigInt.ZERO, BigInt.ONE, BigInt.create(BigInteger.valueOf(polynomialPrecondition.size())));
            final IVariable<BigInt> pCoeffVar = polyInterpretation.getNextCoeff(PolyInterpretation.CONDITIONAL_UNCONDITIONAL_P, pVarRange);

            pCoeffPoly = polyFactory.create(pCoeffVar);

            if (usePrimeFactorization) {
                final Set<BigInt> precondCoeffs = PolyRuleConditionalToUnconditional.collectAbsCoeffs(polynomialPrecondition, PolyRuleConditionalToUnconditional.PRIME_FACTORIZATION_BOUND);
                if (!precondCoeffs.isEmpty()) {
                    final Map<BigInt, Integer> primeFactorization = PolyRuleConditionalToUnconditional.generatePrimeFactorization(precondCoeffs, aborter);
                    final Pair<Polynomial<BigInt>, Set<ItpfPolyAtom<BigInt>>> primeFactorPoly = PolyRuleConditionalToUnconditional.buildCoeffPoly(polyInterpretation, primeFactorization);
                    sideConstraints.addAll(primeFactorPoly.y);
                    pCoeffPoly = pCoeffPoly.mult(primeFactorPoly.x);
                }
            }

            current = conclusionPolyAtom.getPoly().mult(pCoeffPoly);
        } else {
             current = conclusionPolyAtom.getPoly();
             pCoeffPoly = polyFactory.one(ring);
             // else just use 1 as coeffPoly, i.e., no coeff to search for at all
        }

//        System.err.println("CONCLUSION: " + pCoeffPoly + " " + conclusionPolyAtom);

        final Pair<Polynomial<BigInt>, Set<ItpfPolyAtom<BigInt>>> condPrimeFactorPoly;
        final Set<BigInt> conclusionCoeffs = usePrimeFactorization ? PolyRuleConditionalToUnconditional.collectAbsCoeffs(Collections.singleton(conclusionPolyAtom.getPoly()), PolyRuleConditionalToUnconditional.PRIME_FACTORIZATION_BOUND) : null;
        if (usePrimeFactorization && !conclusionCoeffs.isEmpty()) {
            final Map<BigInt, Integer> primeFactorization = PolyRuleConditionalToUnconditional.generatePrimeFactorization(conclusionCoeffs, aborter);
            condPrimeFactorPoly = PolyRuleConditionalToUnconditional.buildCoeffPoly(polyInterpretation, primeFactorization);
        } else {
            condPrimeFactorPoly = new Pair<Polynomial<BigInt>, Set<ItpfPolyAtom<BigInt>>>(
                    polyFactory.one(ring),
                    Collections.<ItpfPolyAtom<BigInt>>emptySet());
        }


        final List<Polynomial<BigInt>> condCoeffs = new ArrayList<Polynomial<BigInt>>(polynomialPrecondition.size());
        for (final Polynomial<BigInt> cond : polynomialPrecondition) {
            final IVariable<BigInt> qCoeffVar = polyInterpretation.getNextCoeff(PolyInterpretation.CONDITIONAL_UNCONDITIONAL_Q, polyInterpretation.getBoolRange());
            final Pair<Polynomial<BigInt>, Set<ItpfPolyAtom<BigInt>>> renamedPrimeFactorPoly = PolyRuleConditionalToUnconditional.renamePrimeFactorPoly(condPrimeFactorPoly, polyInterpretation, PolyInterpretation.CONDITIONAL_UNCONDITIONAL_Q);
            final Polynomial<BigInt> qCoeff = renamedPrimeFactorPoly.x.mult(polyFactory.create(qCoeffVar));
            sideConstraints.addAll(renamedPrimeFactorPoly.y);
            condCoeffs.add(qCoeff);
//            System.err.println("CONDITION: " + qCoeff + " " + cond);
            current = current.subtract(qCoeff.mult(cond));
        }

        final ItpfFactory itpfFactory = polyInterpretation.getConstraintFactory();

        final ItpfPolyAtom<BigInt> unconditional = itpfFactory.createPoly(current, ConstraintType.GE, polyInterpretation);;

        ItpfPolyAtom<BigInt> performanceIncrease = null;

        switch(searchMode) {
        case P_LEQ_Q:
            if (condCoeffs.size() != 1) {
                final Polynomial<BigInt> constraintPoly = polyFactory.add(ring, condCoeffs).subtract(pCoeffPoly).add(polyFactory.one(ring));
                performanceIncrease = itpfFactory.createPoly(constraintPoly, ConstraintType.GE, polyInterpretation);
            }
            break;
        case P_EQ_Q:
            if (!condCoeffs.isEmpty()) {
                final Polynomial<BigInt> constraintPoly = polyFactory.add(ring, condCoeffs).subtract(pCoeffPoly);
                performanceIncrease = itpfFactory.createPoly(constraintPoly, ConstraintType.EQ, polyInterpretation);
            }
            break;
        case P_Q_ONE:
            {
                final Polynomial<BigInt> constraintPoly = polyFactory.add(ring, condCoeffs).subtract(polyFactory.one(ring));
                performanceIncrease = itpfFactory.createPoly(constraintPoly, ConstraintType.EQ, polyInterpretation);
            }
            break;
        }

        sideConstraints.add(unconditional);

        return new Pair<Set<ItpfPolyAtom<BigInt>>, ItpfPolyAtom<BigInt>>(sideConstraints, performanceIncrease);
    }

    private static boolean hasLargeCoeff(final Set<BigInt> precondCoeffs) {
        for (final BigInt coeff : precondCoeffs) {
            if (coeff.compareTo(PolyRuleConditionalToUnconditional.PRIME_FACTORIZATION_BOUND) > 0) {
                return true;
            }
        }
        return false;
    }

    private static Pair<Polynomial<BigInt>, Set<ItpfPolyAtom<BigInt>>> renamePrimeFactorPoly(final Pair<Polynomial<BigInt>, Set<ItpfPolyAtom<BigInt>>> primeFactorPoly,
        final PolyInterpretation<BigInt> polyInterpretation, final String coeffPrefix) {
        final Map<IVariable<?>, IVariable<?>> varRenamingMap = new LinkedHashMap<IVariable<?>, IVariable<?>>();
        for (final IVariable<BigInt> polyVar : primeFactorPoly.x.getVariables()) {
            final IVariable<BigInt> renamed = polyInterpretation.getNextCoeff(coeffPrefix, polyVar.getDomain());
            varRenamingMap.put(polyVar, renamed);
        }

        final VarRenaming varRenaming = VarRenaming.create(ImmutableCreator.create(varRenamingMap), true, polyInterpretation.getFactory());

        final Polynomial<BigInt> renamedPoly = primeFactorPoly.x.applySubstitution(varRenaming);
        final Set<ItpfPolyAtom<BigInt>> renamedConstraints = new LinkedHashSet<ItpfPolyAtom<BigInt>>();
        for (final ItpfPolyAtom<BigInt> polyAtom : primeFactorPoly.y) {
            renamedConstraints.add(polyAtom.applySubstitution(varRenaming));
        }

        return new Pair<Polynomial<BigInt>, Set<ItpfPolyAtom<BigInt>>>(renamedPoly, renamedConstraints);
    }

    /**
     * @return x : coeff polynomial, y : side constraints
     */
    private static Pair<Polynomial<BigInt>, Set<ItpfPolyAtom<BigInt>>> buildCoeffPoly(final PolyInterpretation<BigInt> polyInterpretation,
        final Map<BigInt, Integer> primeFactorization) {
        final SemiRingDomain<BigInt> boolVarRange = polyInterpretation.getBoolRange();
        final BigInt ring = polyInterpretation.getRing();
        final PolyFactory polyFactory = polyInterpretation.getFactory();
        final ItpfFactory itpfFactory = polyInterpretation.getConstraintFactory();
        final Polynomial<BigInt> onePoly = polyFactory.one(ring);

        Polynomial<BigInt> poly = onePoly;

        final Set<ItpfPolyAtom<BigInt>> sideConstraints = new LinkedHashSet<ItpfPolyAtom<BigInt>>();

        if (!primeFactorization.isEmpty()) {
            for (final Map.Entry<BigInt, Integer> primeExp : primeFactorization.entrySet()) {
                final BigInt prime = primeExp.getKey();
                final BigInt primeMinusOne = prime.subtract(BigInt.ONE);
                Monomial<BigInt> lastVarMonomial = null;
                for (int i = primeExp.getValue() - 1; i >= 0; i--) {
                    final IVariable<BigInt> pCoeffVar = polyInterpretation.getNextCoeff(PolyInterpretation.CONDITIONAL_UNCONDITIONAL_P, boolVarRange);
                    poly = poly.mult(onePoly.add(polyFactory.create(primeMinusOne, pCoeffVar, BigInt.ONE)));

                    final Monomial<BigInt> varMonomial = polyFactory.createMonomial(ring, pCoeffVar, BigInt.ONE);
                    if (lastVarMonomial != null) {
                        final LinkedHashMap<Monomial<BigInt>, BigInt> monomials =
                            new LinkedHashMap<Monomial<BigInt>, BigInt>();
                        monomials.put(varMonomial, BigInt.MINUS_ONE);
                        monomials.put(lastVarMonomial, BigInt.ONE);
                        sideConstraints.add(
                            itpfFactory.createPoly(
                                polyFactory.create(
                                    ring,
                                    ImmutableCreator.create(monomials)),
                                ConstraintType.GE,
                                polyInterpretation));
                    }
                    lastVarMonomial = varMonomial;
                }
            }
        }

        return new Pair<Polynomial<BigInt>, Set<ItpfPolyAtom<BigInt>>>(poly, sideConstraints);
    }

    private static Map<BigInt, Integer> generatePrimeFactorization(final Set<BigInt> coeffs, final Abortion aborter) throws AbortionException {
        final Map<BigInt, Integer> maxFactors = new LinkedHashMap<BigInt, Integer>();
        for (final BigInt coeff : coeffs) {
            final Map<BigInt, Integer> factorization = PrimeFactorization.getPrimeFactorization(coeff, aborter);
            for (final Map.Entry<BigInt, Integer> primeExp : factorization.entrySet()) {
                final Integer maxFactor = maxFactors.get(primeExp.getKey());
                if (maxFactor == null) {
                    maxFactors.put(primeExp.getKey(), primeExp.getValue());
                } else {
                    maxFactors.put(primeExp.getKey(), primeExp.getValue().compareTo(maxFactor) > 0 ? primeExp.getValue() : maxFactor);
                }
            }
        }

        return maxFactors;
    }

    private static Set<BigInt> collectAbsCoeffs(final Iterable<Polynomial<BigInt>> polynomialPrecondition, final BigInt bound) {
        final Set<BigInt> coeffs = new LinkedHashSet<BigInt>();

        for (final Polynomial<BigInt> poly : polynomialPrecondition) {
            for (final BigInt coeff : poly.getMonomials().values()) {
                final BigInt absCoeff = coeff.abs();
                if (absCoeff.compareTo(bound) <= 0) {
                    coeffs.add(coeff.abs());
                }
            }
        }

        return coeffs;
    }

    protected static class PreconditionCache extends ReplaceContext.ReplaceContextSkeleton {

        private final LinkedHashMap<ItpfConjClause, Conjunction<Polynomial<BigInt>>> cache;

        public PreconditionCache() {
            this.cache = new LinkedHashMap<ItpfConjClause, Conjunction<Polynomial<BigInt>>>();
        }

        public void put(final ItpfConjClause preconditionClause,
            final Conjunction<Polynomial<BigInt>> result) {
            this.cache.put(preconditionClause, result);
        }

        public Conjunction<Polynomial<BigInt>> get(final ItpfConjClause preconditionClause) {
            return this.cache.get(preconditionClause);
        }

    }

}