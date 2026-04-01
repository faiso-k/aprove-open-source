package aprove.verification.oldframework.Algebra.Polynomials.SMTSearch;

import java.math.*;
import java.util.*;

import aprove.solver.Engines.SMTEngine.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SMTSearch.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Converts Diophantine constraints into linear SMT formulae with the help of an
 * interval for each variable
 *
 * @author Christian Kuknat
 */
public final class DioSMTConverter implements SMTTheoryConverter<Diophantine, SMTLIBIntVariable> {

    private final FormulaFactory<SMTLIBTheoryAtom> factory;

    // we store every variable that occurs in the whole constraint here
    private final Set<String> variables;

    // the interval which is to be moved in
    private DefaultValueMap<String, BigInteger> values;

    // lets map the variables to the smtlibint pendant
    private final Map<String, SMTLIBIntVariable> variableMap;

    private final Set<String> intervalIndefs;

    private final Domain domain;

    public static final BigInteger MIN_BOUND = BigInteger.ZERO;

    private final Splitter splitter;

    private final boolean optimizeValueMap;

    private DioSMTConverter(final FormulaFactory<SMTLIBTheoryAtom> factory,
            final DefaultValueMap<String, BigInteger> values, final Domain domain, final Splitter splitter,
            final boolean optimizeValueMap) {
        this.factory = factory;
        this.values = values;
        this.domain = domain;
        this.splitter = splitter;
        this.optimizeValueMap = optimizeValueMap;
        this.variables = new LinkedHashSet<String>();
        this.variableMap = new LinkedHashMap<String, SMTLIBIntVariable>();
        this.intervalIndefs = new LinkedHashSet<String>();
    }

    public DefaultValueMap<String, BigInteger> getValues() {
        return this.values;
    }

    public void setValues(final DefaultValueMap<String, BigInteger> values) {
        this.values = values;
    }

    public Set<String> getIntervalIndefs() {
        return this.intervalIndefs;
    }

    @Override
    public Map<String, SMTLIBIntVariable> getVariableMap() {
        return this.variableMap;
    }

    public static DioSMTConverter create(final FormulaFactory<SMTLIBTheoryAtom> factory,
        final DefaultValueMap<String, BigInteger> values,
        final Splitter splitter,
        final boolean valueMapOptimizer) {
        return new DioSMTConverter(factory, values, null, splitter, valueMapOptimizer);
    }

    public static DioSMTConverter create(final FormulaFactory<SMTLIBTheoryAtom> factory,
        final Domain domain,
        final Splitter splitter,
        final boolean valueMapOptimizer) {
        return new DioSMTConverter(factory, null, domain, splitter, valueMapOptimizer);
    }

    /**
     * This method converts a Diophantine constraint into a linear one and
     * translates it into SMT for solving the problem in a linear way
     *
     * @param a
     *            Diophantine constraint
     * @return a Formula of SMTLIBIntCMP which can be checked via a SMTSolver
     */
    @Override
    public Formula<SMTLIBTheoryAtom> convert(final Diophantine dio) {

        SimplePolynomial constraint = dio.getLeft();

        // if the Diophantine is sth. like "a > b" we transform it to
        // "a - b > 0" for better handling
        if (dio.getRight() != SimplePolynomial.ZERO) {
            constraint = (dio.getLeft()).minus(dio.getRight());
        }

        for (final IndefinitePart indef : constraint.getSimpleMonomials().keySet()) {
            if (indef.getIndefinites() != null) {
                for (final String var : indef.getIndefinites()) {
                    final SMTLIBIntVariable vari = SMTLIBIntVariable.create(var);
                    if (!this.variables.contains(var)) {
                        this.variables.add(var);
                        if (!this.variableMap.containsKey(var)) {
                            this.variableMap.put(var, vari);
                        }
                    }
                }
            }
        }

        final ConstraintType relation = dio.getRelation();

        // variables = constraint.getindefs

        final Collection<String> usedVars = constraint.getIndefinites();
        final FreshNameGenerator freshNameGen = new FreshNameGenerator(usedVars, FreshNameGenerator.APPEND_NUMBERS);

        Pair<SimplePolynomial, Map<String, IndefinitePart>> linearized = null;

        SimplePolynomial linearConstraint = constraint;
        Map<String, IndefinitePart> toGetCaseDifferentiated = new LinkedHashMap<String, IndefinitePart>();

        // constraint is the lhs - rhs $relation 0!!!!!!
        if (!constraint.isLinear()) {
            linearized = this.linearize(constraint, freshNameGen);
            linearConstraint = linearized.x;

            // we map the new Variable to the IndefinitePart therewith it is
            // necessary to linearize them after it is complete.
            // With this Map it later on has to be possible to transform
            // the solved constrain back to the original form
            toGetCaseDifferentiated = linearized.y;
        }

        // build a Formula<SMTLIBIntCMP> from the linearConstraint
        final SMTLIBIntConstant smtZero = SMTLIBIntConstant.create(BigInteger.ZERO);
        final List<SMTLIBIntValue> smtMonoms = new LinkedList<SMTLIBIntValue>();

        for (final Map.Entry<IndefinitePart, BigInteger> monom : linearConstraint.getSimpleMonomials().entrySet()) {

            final IndefinitePart indef = monom.getKey();
            // the indefinite part of each monom has to be exactly one otherwise
            // it wouldn't be linear thus the transformation was not correct
            assert (indef.getIndefinites().size() <= 1);

            final List<SMTLIBIntValue> values = new ArrayList<SMTLIBIntValue>(2);
            final SMTLIBIntConstant factor = SMTLIBIntConstant.create(monom.getValue());
            values.add(factor);

            if (indef.isIndefinite()) {
                final SMTLIBIntVariable var = this.getVariable(indef.toString());
                values.add(var);
            }

            final SMTLIBIntMult smtMonom = SMTLIBIntMult.create(values);

            smtMonoms.add(smtMonom);
        }
        if (smtMonoms.size() == 0) {
            // just in case somebody forgot to remove 0 >= 0
            smtMonoms.add(smtZero);
        }
        final SMTLIBIntPlus smtPolynomial = SMTLIBIntPlus.create(smtMonoms);

        final SMTLIBIntCMP smtRelation;
        switch (relation) {
        case GT:
            smtRelation = SMTLIBIntGT.create(smtPolynomial, smtZero);
            break;
        case GE:
            smtRelation = SMTLIBIntGE.create(smtPolynomial, smtZero);
            break;
        case EQ:
            smtRelation = SMTLIBIntEquals.create(smtPolynomial, smtZero);
            break;
        default:
            // should never get here!!
            assert (false);
            smtRelation = null;
        }

        assert (smtRelation != null);
        final Formula<SMTLIBTheoryAtom> smtLinearConstraint = this.factory.buildTheoryAtom(smtRelation);

        final List<Formula<SMTLIBTheoryAtom>> smtCompleteLinearized = new LinkedList<Formula<SMTLIBTheoryAtom>>();
        smtCompleteLinearized.add(smtLinearConstraint);

        // now build the caseDiff from the map above
        for (final Map.Entry<String, IndefinitePart> mapping : toGetCaseDifferentiated.entrySet()) {
            final IndefinitePart indef = mapping.getValue();

            // the amount of indefinites has to be exactly 2 or 1 if the
            // transformation till now has been correct because if its higher
            // we would not be linear after case differentiation
            assert (indef.getIndefinites().size() <= 2);

            final Pair<String, Integer> highestExp;
            switch (this.splitter) {
            case HIGHEST_EXP:
                highestExp = this.getSplitterHighestExp(constraint, indef).x;
                break;
            case MOST_OFTEN:
                highestExp = this.getSplitterMostOften(constraint, indef).x;
                break;
            case LEAST_OFTEN:
                highestExp = this.getSplitterLeastOften(constraint, indef).x;
                break;
            case MINIMAL_SET:
                highestExp = this.getSplitterMinimalSet(constraint, indef).x;
                break;
            default:
                throw new UnsupportedOperationException("Should never get here!");
            }
            final IndefinitePart maybeIndef = indef.removeIndefinite(highestExp.getKey());
            String stay = maybeIndef.toString();

            // if there is sth. like x_{a*b*c} = a*y_{b*c} we have to ensure
            // that the case differentiation is done with a not with y_{b*c}
            if (!constraint.containsIndefinite(highestExp.getKey())) {
                // Don't worry about the exponent here because it has to be
                // 1
                final String temp = stay;
                stay = highestExp.getKey();
                highestExp.setKey(temp);
            }

            final SMTLIBIntVariable variable = this.getVariable(mapping.getKey());
            final SMTLIBIntVariable toDifferentiate = this.getVariable(highestExp.getKey());
            final SMTLIBIntVariable smtStay;
            if (maybeIndef.isIndefinite()) {
                smtStay = this.getVariable(stay);
            } else {
                smtStay = null;
            }

            final int exponent = highestExp.getValue();

            // Finally do the fr***ing differentiation!!!
            // consider x_{c*e^2*d} = e^2*y_{c*d}
            // we have to create e = i -> x_{c*e^2*d} = i^2 * y_{c*d}
            // for every i in the domain, or in the range
            if (this.domain != null) {
                final BigInteger lcm = Domain.getLCMofDenominator(this.domain);
                for (final MbyN coeff : this.domain.getDomain()) {
                    BigInteger i = coeff.getNumerator().multiply(lcm);
                    i = i.divide(i.gcd(coeff.getDenominator()));

                    final Formula<SMTLIBTheoryAtom> implication =
                        this.getImplication(i, variable, toDifferentiate, smtStay, exponent);
                    smtCompleteLinearized.add(implication);
                }
                // now just the domain for each variable has
                // to be set for the smt solver
                for (final String indefinite : constraint.getIndefinites()) {

                    // here the variables of the transformation have
                    // to be stored for getting the result later on
                    final SMTLIBIntVariable smtIndef = this.variableMap.get(indefinite.toString());
                    final List<Formula<SMTLIBTheoryAtom>> smtCompleteDomainCase =
                        new LinkedList<Formula<SMTLIBTheoryAtom>>();
                    for (final MbyN coeff : this.domain.getDomain()) {
                        BigInteger i = coeff.getNumerator().multiply(lcm);
                        i = i.divide(i.gcd(coeff.getDenominator()));
                        final SMTLIBIntConstant smtDomain = SMTLIBIntConstant.create(i);
                        final SMTLIBIntEquals smtDomainCase = SMTLIBIntEquals.create(smtIndef, smtDomain);
                        final Formula<SMTLIBTheoryAtom> smtDomainCaseFormula =
                            this.factory.buildTheoryAtom(smtDomainCase);
                        smtCompleteDomainCase.add(smtDomainCaseFormula);
                    }
                    final Formula<SMTLIBTheoryAtom> smtDomainOr = this.factory.buildOr(smtCompleteDomainCase);
                    smtCompleteLinearized.add(smtDomainOr);
                }
            } else if (this.values != null) {
                for (BigInteger i = DioSMTConverter.MIN_BOUND; i.compareTo(this.values.get(highestExp.getKey())) <= 0; i =
                    i.add(BigInteger.ONE)) {
                    final Formula<SMTLIBTheoryAtom> implication =
                        this.getImplication(i, variable, toDifferentiate, smtStay, exponent);
                    smtCompleteLinearized.add(implication);
                }

                // collect indefinites for setting the interval
                for (final String indefinite : constraint.getIndefinites()) {
                    this.intervalIndefs.add(indefinite);
                }
            } else {
                throw new UnsupportedOperationException();
            }
        }
        if (!this.splitBeforeVisit) {
            this.os = null;
        }
        return this.factory.buildAnd(smtCompleteLinearized);
    }

    private Formula<SMTLIBTheoryAtom> getImplication(final BigInteger i,
        final SMTLIBIntVariable variable,
        final SMTLIBIntVariable toDifferentiate,
        final SMTLIBIntVariable smtStay,
        final int exponent) {
        // here we build "e = i", i /in Intervall
        final SMTLIBIntConstant iSMT = SMTLIBIntConstant.create(i);
        final SMTLIBIntCMP thisCase = SMTLIBIntEquals.create(toDifferentiate, iSMT);

        // this is "i^2 * y_{c*d}"
        final List<SMTLIBIntValue> values = new ArrayList<SMTLIBIntValue>();
        values.add(SMTLIBIntConstant.create((i).pow(exponent)));
        if (smtStay != null) {
            values.add(smtStay);
        }

        // now we have "x_{c*e^2*d} = i^2 * y_{c*d}"
        final SMTLIBIntMult thisResult = SMTLIBIntMult.create(values);
        final SMTLIBIntEquals conclusion = SMTLIBIntEquals.create(variable, thisResult);

        // and this is "e = i -> x_{c*e^2*d} = i^2 * y_{c*d}"
        final Formula<SMTLIBTheoryAtom> leftImplicationSide = this.factory.buildTheoryAtom(thisCase);
        final Formula<SMTLIBTheoryAtom> rightImplicationSide = this.factory.buildTheoryAtom(conclusion);
        final Formula<SMTLIBTheoryAtom> implication =
            this.factory.buildImplication(leftImplicationSide, rightImplicationSide);
        return implication;
    }

    private SMTLIBIntVariable getVariable(final String var) {
        SMTLIBIntVariable smtVariable = this.variableMap.get(var);
        if (smtVariable == null) {
            smtVariable = SMTLIBIntVariable.create(var);
        }
        return smtVariable;
    }

    private LinkedHashSet<String> os;
    private boolean splitBeforeVisit = false;

    public void createOs(final int size) {
        this.splitBeforeVisit = true;
        this.os = new LinkedHashSet<String>(size);
    }

    /**
     * This splitter returns the name of the variable which occurs the most
     * often in the whole constraint not regarding it's exponents
     *
     * @param indef
     * @param origConstraint
     * @return a Pair which is exactly an IndefinitePart but as we exactly have
     *         ONE Variable and the corresponding exponent, we use the Pair
     *         instead of the indefinite Part
     */
    private void orderMostOften(final Set<String> unassigned,
        final Set<IndefinitePart> minimalSet,
        final boolean ignoreExponent) {
        if (this.optimizeValueMap) {
            for (final String var : unassigned) {
                if (this.values.get(var).compareTo(this.values.getDefaultValue()) < 0) {
                    this.os.add(var);
                }
            }
        }
        final LinkedHashMap<String, Integer> counts = new LinkedHashMap<String, Integer>();
        for (final String var : unassigned) {
            counts.put(var, 0);
        }
        if (ignoreExponent) {
            for (final IndefinitePart indef : minimalSet) {
                indef.countIndefinites(counts);
            }
        } else {
            for (final IndefinitePart indef : minimalSet) {
                indef.countIndefinitesWithExponent(counts);
            }
        }
        final SortedSet<Integer> sortedInts = new TreeSet<Integer>();
        sortedInts.addAll(counts.values());

        while (!sortedInts.isEmpty()) {
            final int i = sortedInts.last();
            for (final String var : counts.keySet()) {
                if (counts.get(var).compareTo(i) == 0) {
                    this.os.add(var);
                }
            }
            sortedInts.remove(i);
        }
    }

    public void orderMostOftenIgnoreExponent(final Set<String> unassigned, final Set<IndefinitePart> minimalSet) {
        this.orderMostOften(unassigned, minimalSet, true);
    }

    public void orderMostOftenRespectExponent(final Set<String> unassigned, final Set<IndefinitePart> minimalSet) {
        this.orderMostOften(unassigned, minimalSet, false);
    }

    /**
     * This method searches for an order of the variables to make the case
     * differentiation that searches for it with respect to a minimal size after
     * the first variable
     *
     * @param unassigned
     * @param minimalSet
     * @return
     */
    public Set<IndefinitePart> orderForMinimalSet(final Set<String> unassigned, final Set<IndefinitePart> minimalSet) {
        final Set<IndefinitePart> result = new LinkedHashSet<IndefinitePart>();
        if (unassigned.size() > 1) {
            String tempOptVar = null;
            Set<IndefinitePart> tempOptSet = null;
            int max = Integer.MAX_VALUE;
            for (final String variable : unassigned) {

                // case remove whole indef
                final Set<IndefinitePart> newMinimal = new LinkedHashSet<IndefinitePart>();
                newMinimal.addAll(minimalSet);
                for (final IndefinitePart indef : minimalSet) {
                    final IndefinitePart removed = indef.removeIndefinite(variable);
                    if (!removed.isLinear()) {
                        newMinimal.add(removed);
                    }
                }
                final int newMinimalSize = newMinimal.size();

                // nothing to be added so we're done
                if (newMinimalSize == minimalSet.size()) {
                    tempOptVar = variable;
                    tempOptSet = new LinkedHashSet<IndefinitePart>(newMinimal);
                    result.addAll(tempOptSet);
                    break;
                }

                // case decrease indef exponent about one
                final Set<IndefinitePart> newMinimal2 = new LinkedHashSet<IndefinitePart>();
                newMinimal2.addAll(minimalSet);
                for (final IndefinitePart indef : minimalSet) {
                    final IndefinitePart removed = indef.divide(IndefinitePart.create(variable, 1));
                    if (removed != null && !removed.isLinear()) {
                        newMinimal2.add(removed);
                    }
                }
                final int newMinimalSize2 = newMinimal2.size();

                // obviously we added some indef
                if (newMinimalSize <= newMinimalSize2) {
                    if (newMinimalSize <= max) {
                        max = newMinimalSize;
                        tempOptVar = variable;
                        tempOptSet = new LinkedHashSet<IndefinitePart>(newMinimal);
                    }
                } else if (newMinimalSize2 <= max) {
                    max = newMinimalSize2;
                    tempOptVar = variable;
                    tempOptSet = new LinkedHashSet<IndefinitePart>(newMinimal2);
                }
            }
            this.os.add(tempOptVar);
            unassigned.remove(tempOptVar);
            result.addAll(tempOptSet);
            result.addAll(this.orderForMinimalSet(unassigned, tempOptSet));
        }
        this.os.addAll(unassigned);
        return result;
    }

    /**
     * This splitter returns the whole constraint (x) and the name (y) of the variable
     * which leads to a minimized set of intermediate variables after removing this variable
     *
     * @param indef
     * @return a Pair which is exactly an IndefinitePart but as we exactly have
     *         ONE Variable and the corresponding exponent, we use the Pair
     *         instead of the indefinite Part
     */
    private Pair<Pair<String, Integer>, SimplePolynomial> getSplitterMinimalSet(final SimplePolynomial wholeConstraint,
        final IndefinitePart indef) {
        if (this.optimizeValueMap) {
            final BigInteger defaultValue = this.values.getDefaultValue();
            BigInteger lowestFoundValue = this.values.getDefaultValue();
            String lowestFoundKey = null;
            for (final Map.Entry<String, BigInteger> valueEntry : this.values.entrySet()) {
                final String key = valueEntry.getKey();
                if (indef.contains(key) && (lowestFoundValue.compareTo(valueEntry.getValue()) > 0)) {
                    lowestFoundValue = valueEntry.getValue();
                    lowestFoundKey = key;
                }
            }

            if (defaultValue.compareTo(lowestFoundValue) > 0) {
                final Pair<String, Integer> high =
                    new Pair<String, Integer>(lowestFoundKey, indef.getExponent(lowestFoundKey));
                return new Pair<Pair<String, Integer>, SimplePolynomial>(high, wholeConstraint);
            }
        }
        if (null == this.os) {
            final Set<IndefinitePart> indefSet = new LinkedHashSet<IndefinitePart>();
            for (final IndefinitePart indy : wholeConstraint.getSimpleMonomials().keySet()) {
                if (!indy.isLinear()) {
                    indefSet.add(indy);
                }
            }
            final Set<String> unassigned = wholeConstraint.getIndefinites();
            this.os = new LinkedHashSet<String>(unassigned.size());
            this.orderForMinimalSet(unassigned, indefSet);
        }

        String bestExponential = null;
        Integer max = null;
        for (final String var : this.os) {
            if (indef.contains(var)) {
                bestExponential = var;
                max = indef.getExponent(var);
                break;
            }
        }

        final Pair<String, Integer> high = new Pair<String, Integer>(bestExponential, max);
        return new Pair<Pair<String, Integer>, SimplePolynomial>(high, wholeConstraint);
    }

    /**
     * This splitter returns the whole constraint (x) and the name (y) of the variable
     * with the highest exponent of the indefinite part of the polynomial
     *
     * @param indef
     * @return a Pair which is exactly an IndefinitePart but as we exactly have
     *         ONE Variable and the corresponding exponent, we use the Pair
     *         instead of the indefinite Part
     */
    private Pair<Pair<String, Integer>, SimplePolynomial> getSplitterHighestExp(final SimplePolynomial wholeConstraint,
        final IndefinitePart indef) {
        if (this.optimizeValueMap) {
            final BigInteger defaultValue = this.values.getDefaultValue();
            BigInteger lowestFoundValue = this.values.getDefaultValue();
            String lowestFoundKey = null;
            for (final Map.Entry<String, BigInteger> valueEntry : this.values.entrySet()) {
                final String key = valueEntry.getKey();
                if (indef.contains(key) && (lowestFoundValue.compareTo(valueEntry.getValue()) > 0)) {
                    lowestFoundValue = valueEntry.getValue();
                    lowestFoundKey = key;
                }
            }

            if (defaultValue.compareTo(lowestFoundValue) > 0) {
                final Pair<String, Integer> high =
                    new Pair<String, Integer>(lowestFoundKey, indef.getExponent(lowestFoundKey));
                return new Pair<Pair<String, Integer>, SimplePolynomial>(high, wholeConstraint);
            }
        }
        int max = 0;
        String highestExponential = null;
        for (final Map.Entry<String, Integer> exponent : indef.getExponents().entrySet()) {
            if (exponent.getValue() >= max) {
                highestExponential = exponent.getKey();
                max = exponent.getValue();
            }
        }

        final Pair<String, Integer> high = new Pair<String, Integer>(highestExponential, max);
        return new Pair<Pair<String, Integer>, SimplePolynomial>(high, wholeConstraint);
    }

    /**
     * This splitter returns the name of the variable which occurs the most
     * often in the whole constraint, that is given
     *
     * @param indef
     * @param origConstraint
     * @return a Pair which is exactly an IndefinitePart but as we exactly have
     *         ONE Variable and the corresponding exponent, we use the Pair
     *         instead of the indefinite Part
     */
    private Pair<Pair<String, Integer>, SimplePolynomial> getSplitterMostOften(final SimplePolynomial origConstraint,
        final IndefinitePart indef) {
        if (this.optimizeValueMap) {
            final BigInteger defaultValue = this.values.getDefaultValue();
            BigInteger lowestFoundValue = this.values.getDefaultValue();
            String lowestFoundKey = null;
            for (final Map.Entry<String, BigInteger> valueEntry : this.values.entrySet()) {
                final String key = valueEntry.getKey();
                if (indef.contains(key) && (lowestFoundValue.compareTo(valueEntry.getValue()) > 0)) {
                    lowestFoundValue = valueEntry.getValue();
                    lowestFoundKey = key;
                }
            }

            if (defaultValue.compareTo(lowestFoundValue) > 0) {
                final Pair<String, Integer> high =
                    new Pair<String, Integer>(lowestFoundKey, indef.getExponent(lowestFoundKey));
                return new Pair<Pair<String, Integer>, SimplePolynomial>(high, origConstraint);
            }
        }
        int max = -1;
        String mostOften = null;
        final LinkedHashMap<String, Integer> counts = new LinkedHashMap<String, Integer>();
        for (final IndefinitePart entry : origConstraint.getSimpleMonomials().keySet()) {
            entry.countIndefinites(counts);
        }
        for (final Map.Entry<String, Integer> entry : counts.entrySet()) {
            final int count = entry.getValue();
            final String indy = entry.getKey();
            if (count > max && indef.contains(indy)) {
                mostOften = indy;
                max = count;
            }
        }
        final Pair<String, Integer> high = new Pair<String, Integer>(mostOften, indef.getExponent(mostOften));
        return new Pair<Pair<String, Integer>, SimplePolynomial>(high, origConstraint);
    }

    /**
     * This splitter returns the name of the variable which occurs the most
     * often in the whole constraint, that is given
     *
     * @param indef
     * @param origConstraint
     * @return a Pair which is exactly an IndefinitePart but as we exactly have
     *         ONE Variable and the corresponding exponent, we use the Pair
     *         instead of the indefinite Part
     */
    private Pair<Pair<String, Integer>, SimplePolynomial> getSplitterLeastOften(final SimplePolynomial origConstraint,
        final IndefinitePart indef) {
        if (this.optimizeValueMap) {
            final BigInteger defaultValue = this.values.getDefaultValue();
            BigInteger lowestFoundValue = this.values.getDefaultValue();
            String lowestFoundKey = null;
            for (final Map.Entry<String, BigInteger> valueEntry : this.values.entrySet()) {
                final String key = valueEntry.getKey();
                if (indef.contains(key) && (lowestFoundValue.compareTo(valueEntry.getValue()) > 0)) {
                    lowestFoundValue = valueEntry.getValue();
                    lowestFoundKey = key;
                }
            }

            if (defaultValue.compareTo(lowestFoundValue) > 0) {
                final Pair<String, Integer> high =
                    new Pair<String, Integer>(lowestFoundKey, indef.getExponent(lowestFoundKey));
                return new Pair<Pair<String, Integer>, SimplePolynomial>(high, origConstraint);
            }
        }
        int max = Integer.MAX_VALUE;
        String mostOften = null;
        final LinkedHashMap<String, Integer> counts = new LinkedHashMap<String, Integer>();
        for (final IndefinitePart entry : origConstraint.getSimpleMonomials().keySet()) {
            entry.countIndefinites(counts);
        }
        for (final Map.Entry<String, Integer> entry : counts.entrySet()) {
            final int count = entry.getValue();
            final String indy = entry.getKey();
            if (count < max && indef.contains(indy)) {
                mostOften = indy;
                max = count;
            }
        }
        final Pair<String, Integer> high = new Pair<String, Integer>(mostOften, indef.getExponent(mostOften));
        return new Pair<Pair<String, Integer>, SimplePolynomial>(high, origConstraint);
    }

    private Pair<SimplePolynomial, Map<String, IndefinitePart>> linearize(final SimplePolynomial constraint,
        final FreshNameGenerator freshNameGen) {
        final Map<String, IndefinitePart> variableMapping = new LinkedHashMap<String, IndefinitePart>();
        Map<String, IndefinitePart> newVariableMapping = new LinkedHashMap<String, IndefinitePart>();

        final SimplePolynomial linearConstraint = this.abstractIt(constraint, freshNameGen, variableMapping);

        // now the constraint itself is linear but the abstracted new variables
        // has to be linearized
        newVariableMapping = this.linearizeIt(variableMapping, freshNameGen, linearConstraint, constraint);

        return new Pair<SimplePolynomial, Map<String, IndefinitePart>>(linearConstraint, newVariableMapping);
    }

    /**
     * This method builds a linear constraint out of the original one and builds
     * up the Variable map for the case differential later on
     *
     * @param constraint
     *            which has to get linearized
     * @param freshNameGen
     *            for creating new variables x_ab for x_{a*b} = a*b
     * @param newVariableMap
     *            for storing which variables have to get case differentiated
     * @return
     */
    private SimplePolynomial abstractIt(final SimplePolynomial constraint,
        final FreshNameGenerator freshNameGen,
        final Map<String, IndefinitePart> newVariableMap) {
        SimplePolynomial linearConstraint = SimplePolynomial.create(BigInteger.ZERO);

        for (final Map.Entry<IndefinitePart, BigInteger> monom : constraint.getSimpleMonomials().entrySet()) {
            final IndefinitePart indef = monom.getKey();
            final BigInteger factor = monom.getValue();

            if (!indef.isLinear()) {
                // introduce a new linear variable e.g. for 3*a*b^2 we have
                // 3x_{a*b^2} use false here if we don't want to memorize the
                // renaming
                final String newVarName = freshNameGen.getFreshName("x_{" + indef.toString() + "}", true);
                final IndefinitePart newVariable = IndefinitePart.create(newVarName, 1);
                // me put the new Variable into our mapping such that we can
                // transform it later on into further linear constraints and do
                // the case differentiation
                newVariableMap.put(newVariable.toString(), indef);

                // now we build up the constraint with all linear monoms
                linearConstraint = linearConstraint.plus(SimplePolynomial.create(newVariable, factor));
            } else {
                // the monomial is linear thus we don't need to linearize or
                // abstract it any further
                linearConstraint = linearConstraint.plus(SimplePolynomial.create(indef, factor));
            }

        }
        return linearConstraint;
    }

    /**
     * This method linearizes the additional variables that have been created
     *
     * @param variableMapping
     *            the map which is build up and gets added with all linear
     *            variables
     * @param freshNameGen
     *            for creating new variables x_ab for x_{a*b} = a*b
     * @param newVariableMap
     *            for storing which variables have to get case differentiated
     */
    private Map<String, IndefinitePart> linearizeIt(final Map<String, IndefinitePart> variableMapping,
        final FreshNameGenerator freshNameGen,
        final SimplePolynomial constraint,
        final SimplePolynomial origConstraint) {
        final Map<String, IndefinitePart> newVariableMapping = new LinkedHashMap<String, IndefinitePart>();
        final Map<String, IndefinitePart> newIteration = new LinkedHashMap<String, IndefinitePart>();
        // we iterate over the map of new variables, look up if they have one
        // variable like a^x and another one such that the whole constraint
        // looks like a^x * b for b is linear if this is not the case we build
        // up a new variable in this Map and linearize them again
        for (final Map.Entry<String, IndefinitePart> linearizables : variableMapping.entrySet()) {
            final IndefinitePart indef = linearizables.getValue();
            final String variable = linearizables.getKey();
            Pair<String, Integer> splitter;
            switch (this.splitter) {
            case HIGHEST_EXP:
                splitter = this.getSplitterHighestExp(constraint, indef).x;
                break;
            case MOST_OFTEN:
                splitter = this.getSplitterMostOften(origConstraint, indef).x;
                break;
            case LEAST_OFTEN:
                splitter = this.getSplitterLeastOften(origConstraint, indef).x;
                break;
            case MINIMAL_SET:
                splitter = this.getSplitterMinimalSet(origConstraint, indef).x;
                break;
            default:
                throw new UnsupportedOperationException();
            }
            final IndefinitePart removedHighestExponential = indef.removeIndefinite(splitter.x);
            if (removedHighestExponential.isLinear()) {
                newVariableMapping.put(variable, indef);
            } else {
                final String newVarName =
                    freshNameGen.getFreshName("y_{" + removedHighestExponential.toString() + "}", true);
                final IndefinitePart toBeCaseDifferentiated = IndefinitePart.create(splitter.x, splitter.y);
                final IndefinitePart newVariable = IndefinitePart.create(newVarName, 1);
                newVariableMapping.put(variable, newVariable.times(toBeCaseDifferentiated));
                newIteration.put(newVarName, removedHighestExponential);
            }
        }
        if (!newIteration.isEmpty()) {
            newVariableMapping.putAll(this.linearizeIt(newIteration, freshNameGen, constraint, origConstraint));
        }
        return newVariableMapping;
    }

}
