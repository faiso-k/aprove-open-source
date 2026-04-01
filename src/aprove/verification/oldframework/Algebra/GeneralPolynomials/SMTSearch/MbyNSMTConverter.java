package aprove.verification.oldframework.Algebra.GeneralPolynomials.SMTSearch;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatFunctions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Converts OPC<MbyN> constraints of the FLAT, quantor - killed form
 * "a*xy + b xz $relation 0" into linear SMT formulae with the help of an
 * interval or domain for each variable
 *
 * @author Christian Kuknat
 */
public class MbyNSMTConverter implements
        SMTTheoryConverter<OrderPolyConstraint<MbyN>, SMTLIBRatVariable> {

    private FormulaFactory<SMTLIBTheoryAtom> factory;

    // we store every variable that occures in the whole constraint here
    private Set<String> variables;

    // the interval which is to be moved in
    private DefaultValueMap<String, BigInteger> values;

    // lets map the variables to the smtlibrat pendant
    private Map<String, SMTLIBRatVariable> variableMap;

    private Domain domain;

    /**
     * The flattening visitor for order polynomials.
     */
    private FlatteningVisitor<GPoly<MbyN, GPolyVar>, GPolyVar> fvOuter;

    private static final BigInteger MIN_BOUND = BigInteger.ZERO;

    @Override
    public Map<String, SMTLIBRatVariable> getVariableMap() {
        return this.variableMap;
    }

    OrderPolyFactory<MbyN> orderPolyFactory;

    private Ring<MbyN> innerRing;
    private Ring<GPoly<MbyN, GPolyVar>> outerRing;
    private CMonoid<GMonomial<GPolyVar>> monoid;
    /**
     * A frequently used pair containing the ring and monoid used to access the
     * monomials.
     */
    private Pair<Semiring<GPoly<MbyN, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>> pair;

    public void setRings(Ring<GPoly<MbyN, GPolyVar>> outerRing,
            Ring<MbyN> innerRing, CMonoid<GMonomial<GPolyVar>> monoid) {
        this.outerRing = outerRing;
        this.innerRing = innerRing;
        this.monoid = monoid;
        this.pair = new Pair<Semiring<GPoly<MbyN, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>>(
                this.outerRing, this.monoid);
    }

    public MbyNSMTConverter(FormulaFactory<SMTLIBTheoryAtom> factory,
            Domain domain,
            FlatteningVisitor<GPoly<MbyN, GPolyVar>, GPolyVar> fvOuter) {
        this.factory = factory;
        this.domain = domain;
        this.fvOuter = fvOuter;
        this.variables = new LinkedHashSet<String>();
        this.variableMap = new LinkedHashMap<String, SMTLIBRatVariable>();
        GPolyFactory<MbyN, GPolyVar> gPolyCoeffFactory = new aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.FullSharingFactory<MbyN, GPolyVar>();
        GPolyFactory<GPoly<MbyN, GPolyVar>, GPolyVar> gPolyCoeffFactory2 = new aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.FullSharingFactory<GPoly<MbyN, GPolyVar>, GPolyVar>();
        this.orderPolyFactory = new OrderPolyFactory<MbyN>(gPolyCoeffFactory2,
                gPolyCoeffFactory);
    }

    private boolean isLinear(OrderPoly<MbyN> orderPoly) {
        for (GMonomial<GPolyVar> monomial : orderPoly.getMonomials(this.pair)
                .keySet()) {
            if (monomial.getDegree().compareTo(BigInteger.ONE) > 0) {
                return false;
            }
        }
        return true;
    }

    private boolean isLinear(GMonomial<GPolyVar> monomial) {
        return (monomial.getDegree().compareTo(BigInteger.ONE) <= 0);
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
    public Formula<SMTLIBTheoryAtom> convert(
            OrderPolyConstraint<MbyN> opc) {
        // this.variableMap.clear();
        // this.variables.clear();

        // if not the case the visitor did sth. wrong before ... I think
        assert(opc instanceof OPCAtom<?>);
        OPCAtom<MbyN> opca = (OPCAtom<MbyN>) opc;
        /*
         * As mentioned in MbyNtoFormula.java we only consider the left side
         * as the right one has to be zero in what way ever
         */
        OrderPoly<MbyN> constraint = opca.getLeftPoly();

//        for(Entry<GMonomial<GPolyVar>, GPoly<MbyN, GPolyVar>> entry : constraint.getMonomials(this.pair).entrySet()) {
//            GMonomial<GPolyVar> monomial = entry.getKey();
//            GPoly<MbyN, GPolyVar> coeffPoly = entry.getValue();
        /*
         * Store all variables of the OrderPoly in relation to their smt - pendant
         */
        for (GPolyVar var : constraint.getVariables()) {
            if (var != null) {
                String name = var.getName();
                if (!this.variables.contains(name)) {
                    this.variables.add(name);
                    SMTLIBRatVariable smtVariable = SMTLIBRatVariable
                            .create(name);
                    this.variableMap.put(name, smtVariable);
                }
            }
        }

        ConstraintType relation = opca.getConstraintType();

        // Create fresh name generator, for creating the new variables later on
        FreshNameGenerator freshNameGen = new FreshNameGenerator(this.variables,
                FreshNameGenerator.APPEND_NUMBERS);

        /*
         * This later on is a pair of the constraint of the beginning and
         * a mapping of the new variables to their former actual variables
         */
        Pair<OrderPoly<MbyN>, Map<String, GMonomial<GPolyVar>>> linearized = null;

        OrderPoly<MbyN> linearConstraint = constraint;
        Map<String, GMonomial<GPolyVar>> toGetCaseDifferentiated = new LinkedHashMap<String, GMonomial<GPolyVar>>();

        // constraint is the lhs - rhs $relation$ 0!!!!!!
        if (!this.isLinear(constraint)) {
            linearized = this.linearize(constraint, freshNameGen);
            linearConstraint = linearized.x;

            // we map the new Variable to the IndefinitePart therewith it is
            // necessary to linearize them after it is complete.
            // With this Map it later on has to be possible to transform
            // the solved constrain back to the original form
            toGetCaseDifferentiated = linearized.y;
        }

        // build a Formula<SMTLIBRatCMP> from the linearConstraint
        SMTLIBRatConstant smtZero =
            SMTLIBRatConstant.create(BigInteger.ZERO);
        List<SMTLIBRatValue> smtMonoms = new LinkedList<SMTLIBRatValue>();

        for (Entry<GMonomial<GPolyVar>, GPoly<MbyN, GPolyVar>> monom : linearConstraint
                .getMonomials(this.pair).entrySet()) {
            GMonomial<GPolyVar> indef = monom.getKey();

            // the indefinite part of each monom has to be exactly one otherwise
            // it wouldn't be linear thus the transformation was not correct
            // thus there should only be one entry for the exponents of the monomials
            assert (indef.getExponents().size() <= 1);

            List<SMTLIBRatValue> values = new ArrayList<SMTLIBRatValue>(2);
            int i = 0;
            for (MbyN mn : monom.getValue().getCoeffs()) {
                if (mn != null) {
                    i++;
                }
            }
            assert (i == 1) : "Ask Carsten why this is not flat!";
            SMTLIBRatConstant factor = SMTLIBRatConstant.create(monom
                    .getValue().getCoeffs().get(0));
            values.add(factor);

            // Don't blame me, this is the translation of isIndefinite of IndefinitePart into GMonomial
            if (indef.getExponents().size() == 1 && indef.getExponents().values().contains(BigInteger.ONE)) {
                SMTLIBRatVariable var = this.getVariable(indef.toString());
                values.add(var);
            }

            SMTLIBRatMult smtMonom = SMTLIBRatMult.create(values);

            smtMonoms.add(smtMonom);
        }
        if (smtMonoms.size() == 0) {
            smtMonoms.add(smtZero);
        }
        SMTLIBRatPlus smtPolynomial = SMTLIBRatPlus.create(smtMonoms);

        SMTLIBRatCMP smtRelation = null;
        switch (relation) {
        case GT:
            smtRelation = SMTLIBRatGT.create(smtPolynomial, smtZero);
            break;
        case GE:
            smtRelation = SMTLIBRatGE.create(smtPolynomial, smtZero);
            break;
        case EQ:
            smtRelation = SMTLIBRatEquals.create(smtPolynomial, smtZero);
            break;
        default:
            // should never get here!!
            assert (false);
        }

        assert (smtRelation != null);
        Formula<SMTLIBTheoryAtom> smtLinearConstraint = this.factory
        .buildTheoryAtom(smtRelation);

        List<Formula<SMTLIBTheoryAtom>> smtCompleteLinearized = new
        LinkedList<Formula<SMTLIBTheoryAtom>>();
        smtCompleteLinearized.add(smtLinearConstraint);

        // now build the caseDiff from the map above
        for (Map.Entry<String, GMonomial<GPolyVar>> mapping : toGetCaseDifferentiated
                .entrySet()) {
            GMonomial<GPolyVar> indef = mapping.getValue();

            // the amount of indefinites has to be exactly 2 or 1 if the
            // transformation till now has been correct because if its higher
            // we would not be linear after case differentiation
            assert (indef.getExponents().size() <= 2);

            // if the indef is
            Pair<GPolyVar, BigInteger> highestExp = this
                    .getSplitter(
                    constraint,
                    indef).x;

            // Fuck immutable map without any remove possibility ;)
            Map<GPolyVar, BigInteger> tempNotImmutableMonomialMap = new LinkedHashMap<GPolyVar, BigInteger>(
                    indef.getExponents());
            tempNotImmutableMonomialMap.remove(highestExp.getKey());
            GMonomial<GPolyVar> removedHighestExponential = new GMonomial<GPolyVar>(
                    tempNotImmutableMonomialMap);

            String stay = removedHighestExponential.toString();
            String highestExpString = highestExp.getKey().toString();

            // if there is sth. like x_{a*b*c} = a*y_{b*c} we have to ensure
            // that the case differentiation is done with a not with y_{b*c}
            if (!constraint.getVariables().contains(highestExp.getKey())) {
                // Don't worry about the exponent here because it has to be 1
                String temp = stay;
                stay = highestExpString;
                highestExpString = temp;
            }

            SMTLIBRatVariable variable = this.getVariable(mapping.getKey());
            SMTLIBRatVariable toDifferentiate = this.getVariable(highestExpString);
            SMTLIBRatVariable smtStay = null;
            if (!removedHighestExponential.getExponents().isEmpty()) {
                smtStay = this.getVariable(stay);
            }

            BigInteger exponent = highestExp.getValue();

            MbyNRing ring = new MbyNRing();
            // Finally do the fr***ing differentiation!!!
            // consider x_{c*e^2*d} = e^2*y_{c*d}
            for (MbyN i : this.domain.getDomain()) {
                // here we build "e = i", i /in Intervall
                SMTLIBRatConstant iSMT = SMTLIBRatConstant.create(i);
                SMTLIBRatCMP thisCase = SMTLIBRatEquals.create(toDifferentiate,
                        iSMT);

                // this is "i^2 * y_{c*d}"
                List<SMTLIBRatValue> values = new ArrayList<SMTLIBRatValue>();
                MbyN temp = i;
                for (BigInteger j = BigInteger.ONE; j.compareTo(exponent) < 0; j = j
                        .add(BigInteger.ONE)) {
                    temp = ring.times(temp, i);
                }
                values.add(SMTLIBRatConstant.create(temp));
                if (smtStay != null) {
                    values.add(smtStay);
                }
                SMTLIBRatMult thisResult = SMTLIBRatMult.create(values);
                // now we have "x_{c*e^2*d} = i^2 * y_{c*d}"
                SMTLIBRatEquals conclusion = SMTLIBRatEquals.create(variable,
                        thisResult);

                // and this is "e = i -> x_{c*e^2*d} = i^2 * y_{c*d}" ... I hope
                Formula<SMTLIBTheoryAtom> leftImplicationSide = this.factory
                .buildTheoryAtom(thisCase);
                Formula<SMTLIBTheoryAtom> rightImplicationSide = this.factory
                .buildTheoryAtom(conclusion);
                Formula<SMTLIBTheoryAtom> implication = this.factory
                .buildImplication(leftImplicationSide,
                        rightImplicationSide);
                smtCompleteLinearized.add(implication);
            }
        }

        // now just the interval as a domain for each variable
        // has to be set for the smt solver
        for (String indefinite : this.variables) {
            List<Formula<SMTLIBTheoryAtom>> domOr = new
            LinkedList<Formula<SMTLIBTheoryAtom>>();
            for (MbyN i : this.domain.getDomain()) {
                // here the variables of the transformation have
                // to be stored for getting the result later on
                SMTLIBRatVariable smtIndef = this.getVariable(indefinite
                        .toString());
                SMTLIBRatConstant domConst = SMTLIBRatConstant.create(i);
                SMTLIBRatEquals equal = SMTLIBRatEquals.create(smtIndef,
                        domConst);
                Formula<SMTLIBTheoryAtom> domFormulaAtom = this.factory
                .buildTheoryAtom(equal);
                domOr.add(domFormulaAtom);
            }
            smtCompleteLinearized.add(this.factory.buildOr(domOr));
        }
        return this.factory.buildAnd(smtCompleteLinearized);
    }

    private SMTLIBRatVariable getVariable(String var) {
        SMTLIBRatVariable smtVariable = this.variableMap.get(var);
        if (smtVariable == null) {
            smtVariable = SMTLIBRatVariable.create(var);
        }
        return smtVariable;
    }

    /**
     * This splitter returns the whole constraint (x) and the name (y) of the
     * variable with the highest exponent of the indefinite part of the
     * polynomial
     *
     * @param indef
     * @return a Pair which is exactly an IndefinitePart but as we exactly have
     *         ONE Variable and the corresponding exponent, we use the Pair
     *         instead of the indefinite Part
     */
    private Pair<Pair<GPolyVar, BigInteger>, OrderPoly<MbyN>> getSplitter(
            OrderPoly<MbyN> wholeConstraint, GMonomial<GPolyVar> monomial) {
        BigInteger max = BigInteger.ZERO;
        GPolyVar highestExponential = null;
        for (Entry<GPolyVar, BigInteger> exponent : monomial.getExponents()
                .entrySet()) {
            if (exponent.getValue().compareTo(max) >= 0) {
                highestExponential = exponent.getKey();
                max = exponent.getValue();
            }
        }

        Pair<GPolyVar, BigInteger> high = new Pair<GPolyVar, BigInteger>(
                highestExponential, max);
        return new Pair<Pair<GPolyVar, BigInteger>, OrderPoly<MbyN>>(high,
                wholeConstraint);
    }

    /**
     * This splitter returns the name of the variable which occures the most
     * often in the whole constraint, that is given
     *
     * @param indef
     * @return a Pair which is exactly an IndefinitePart but as we exactly have
     *         ONE Variable and the corresponding exponent, we use the Pair
     *         instead of the indefinite Part
     */
    private Pair<Pair<GPolyVar, BigInteger>, OrderPoly<MbyN>> getSplitter2(
            OrderPoly<MbyN> wholeConstraint, GMonomial<GPolyVar> monomial) {
        BigInteger max = BigInteger.ZERO;
        GPolyVar highestExponential = null;
        for (String var : this.variables) {
            BigInteger sum = BigInteger.ZERO;
            GPolyVar temp = new GAtomicVar(var);
            for (GMonomial<GPolyVar> monom : wholeConstraint.getMonomials(
                    this.pair)
                    .keySet()) {
                sum = sum.add(monom.getExponent(temp));
            }
            if (sum.compareTo(max) >= 0) {
                max = sum;
                highestExponential = temp;
            }
        }
        Pair<GPolyVar, BigInteger> high = new Pair<GPolyVar, BigInteger>(
                highestExponential, monomial.getExponent(highestExponential));
        // might want to delete the variable given Back by this method
        // SimplePolynomial newConstraint = wholeConstraint.getSimpleMonomials()

        // delete the variable from the set of variables (this.variables) which
        // is used by var
        return new Pair<Pair<GPolyVar, BigInteger>, OrderPoly<MbyN>>(high,
                wholeConstraint);
    }

    // TODO neuer splitter nach valueMap (kleinstes Intervall wird
    // fallunterschieden)

    private Pair<OrderPoly<MbyN>, Map<String, GMonomial<GPolyVar>>> linearize(
            OrderPoly<MbyN> constraint, FreshNameGenerator freshNameGen) {
        Map<String, GMonomial<GPolyVar>> variableMapping = new LinkedHashMap<String, GMonomial<GPolyVar>>();
        Map<String, GMonomial<GPolyVar>> newVariableMapping = new LinkedHashMap<String, GMonomial<GPolyVar>>();

        OrderPoly<MbyN> linearConstraint = this.abstractIt(constraint,
                freshNameGen, variableMapping);

        // now the constraint itself is linear but the abstracted new variables
        // has to be linearized
        newVariableMapping = this.linearizeIt(variableMapping, freshNameGen,
                linearConstraint);

        return new Pair<OrderPoly<MbyN>, Map<String, GMonomial<GPolyVar>>>(
                linearConstraint, newVariableMapping);
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
    private OrderPoly<MbyN> abstractIt(OrderPoly<MbyN> constraint,
            FreshNameGenerator freshNameGen,
            Map<String, GMonomial<GPolyVar>> newVariableMap) {

        OrderPoly<MbyN> linearConstraint = this.orderPolyFactory.getZero();

        for (Map.Entry<GMonomial<GPolyVar>, GPoly<MbyN, GPolyVar>> monom : constraint
                .getMonomials(this.pair).entrySet()) {
            GMonomial<GPolyVar> indef = monom.getKey();
            GPoly<MbyN, GPolyVar> factor = monom.getValue();

            if (!this.isLinear(indef)) {
                // introduce a new linear variable e.g. for 3*a*b^2 we have
                // 3x_{a*b^2} use false here if we don't want to memorize the
                // renaming
                String newVarName = freshNameGen.getFreshName("x_{"
                        + indef.toString() + "}", true);
                GPolyVar newVariable = new GAtomicVar(newVarName);
                GMonomial<GPolyVar> newMonomial = new GMonomial<GPolyVar>(
                        newVariable);
                VarPartNode<GPolyVar> varPartNode = VarPartNode
                        .fromMonomial(newMonomial);
                OrderPoly<MbyN> newOrderPoly = this.orderPolyFactory.concat(factor,
                        varPartNode);
                // me put the new Variable into our mapping such that we can
                // transform it later on into further linear constraints and do
                // the case differentiation
                newVariableMap.put(newVariable.toString(), indef);

                // now we build up the constraint with all linear monoms
                linearConstraint = this.orderPolyFactory.plus(linearConstraint,
                        newOrderPoly);
            } else {
                // the monom is linear thus we don't need to linearize or
                // abstract it any further
                VarPartNode<GPolyVar> varPartNode = VarPartNode
                        .fromMonomial(indef);
                OrderPoly<MbyN> op = this.orderPolyFactory.concat(factor,
                        varPartNode);
                linearConstraint = this.orderPolyFactory.plus(linearConstraint, op);
            }

        }
        this.fvOuter.applyTo(linearConstraint);
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
    private Map<String, GMonomial<GPolyVar>> linearizeIt(
            Map<String, GMonomial<GPolyVar>> variableMapping,
            FreshNameGenerator freshNameGen, OrderPoly<MbyN> constraint) {
        Map<String, GMonomial<GPolyVar>> newVariableMapping = new LinkedHashMap<String, GMonomial<GPolyVar>>();
        Map<String, GMonomial<GPolyVar>> newIteration = new LinkedHashMap<String, GMonomial<GPolyVar>>();
        // we iterate over the map of new variables, look up if they have one
        // variable like a^x and another one such that the whole constraint
        // looks like a^x * b for b is linear if this is not the case we build
        // up a new variable in this Map and linearize them again
        for (Map.Entry<String, GMonomial<GPolyVar>> linearizables : variableMapping
                .entrySet()) {
            GMonomial<GPolyVar> monomial = linearizables.getValue();
            String variable = linearizables.getKey();
            Pair<GPolyVar, BigInteger> highestExp = this.getSplitter(
                    constraint,
                    monomial).x;
            // Fuck immutable map without any remove possibility ;)
            Map<GPolyVar, BigInteger> newMonomialMap = new LinkedHashMap<GPolyVar, BigInteger>(
                    monomial.getExponents());
            newMonomialMap.remove(highestExp.getKey());
            GMonomial<GPolyVar> removedHighestExponential = new GMonomial<GPolyVar>(
                    newMonomialMap);
            if (this.isLinear(removedHighestExponential)) {
                newVariableMapping.put(variable, monomial);
            } else {
                String newVarName = freshNameGen.getFreshName("y_{"
                        + removedHighestExponential.toString() + "}", true);
                GPolyVar newPolyVar = new GAtomicVar(newVarName);
                Map<GPolyVar, BigInteger> monomialMap = new LinkedHashMap<GPolyVar, BigInteger>();
                monomialMap.put(highestExp.x, highestExp.y);
                monomialMap.put(newPolyVar, BigInteger.ONE);
                GMonomial<GPolyVar> newMonomial = new GMonomial<GPolyVar>(
                        monomialMap);

                newVariableMapping.put(variable, newMonomial);
                assert (removedHighestExponential != null) : "this would lead to null pointer";
                if (removedHighestExponential.getDegree().compareTo(
                        BigInteger.ZERO) > 0) {
                    newIteration.put(newVarName, removedHighestExponential);
                }
            }
        }
        if (!newIteration.isEmpty()) {
            newVariableMapping.putAll(this.linearizeIt(newIteration, freshNameGen,
                    constraint));
        }
        return newVariableMapping;
    }

}
