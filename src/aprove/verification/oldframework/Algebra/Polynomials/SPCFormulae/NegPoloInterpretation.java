package aprove.verification.oldframework.Algebra.Polynomials.SPCFormulae;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.solver.*;
import aprove.solver.NEGPOLOFactory.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.NegativePolynomials.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.QApplicativeUsableRules.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * SAT solving for finding Polynomial Orders with Negative Constants.
 * Described in more detail in the paper:
 *
 * C. Fuhs, J. Giesl, A. Middeldorp, P. Schneider-Kamp, R. Thiemann, H. Zankl
 * SAT Solving for Termination Analysis with Polynomial Interpretations
 * Proc. SAT'07, LNCS 4501, pp. 340-354, 2007.
 *
 * Meanwhile improved by several optimizations -- no need to consider the case
 * of negative constants for /all/ function symbols.
 *
 * @author thiemann
 * @author fuhs
 * @version $Id$
 */
public class NegPoloInterpretation {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.SPCFormulae.NegPoloInterpretation");

    private static final String COEFF_PREFIX = "a_";
    private static final String VARIABLE_PREFIX = "x_";

    private final List<Formula<Diophantine>> sideConditions;
    // stores the global formula psi and later on the rule constraints, too

    private final Map<FunctionSymbol, VarPolynomial> interpretation; // the interpretation
    private int nextCoeff; // for creating new coefficients
    private final BigIntegerInterval coeffRange; // the range for coefficients
    private final BigInteger constNegRange; // the negative border for a constant
    private final BigIntegerInterval constRange; // the range for constants (which has to be shifted by constNegRange)
    private final BigIntegerInterval constPosRange; // the range for the interpretation of 0-ary symbols
    private final NegRangeCriterion negRangeCriterion; // criterion for which symbols we try negative ranges

    private final Map<TRSTerm, VarPolynomial> memoryLeft, memoryRight; // (unbounded) caches for interpretation

    private final Map<String, BigIntegerInterval> ranges;

    private final FormulaFactory<Diophantine> factory;

    // will be filled and checked iff negRangeCriterion == DAMPEN
    private final Set<FunctionSymbol> potentiallyNegativeSymbols;

    // optimization: use explicit Diophantine variables for b_t^left only
    // where b_t (the real constant) and b_t^left (the approximated constant)
    // might actually differ
    private final boolean partialDioEval;

    private NegPoloInterpretation(BigInteger coeffRange,
            BigInteger constPosRange, BigInteger constNegRange,
            NegRangeCriterion negRangeCriterion,
            boolean partialDioEval) {
        this.sideConditions = new ArrayList<Formula<Diophantine>>();
        this.interpretation = new LinkedHashMap<FunctionSymbol, VarPolynomial>();
        this.nextCoeff = 0;
        this.coeffRange = new BigIntegerInterval(BigInteger.ZERO, coeffRange);
        this.constNegRange = constNegRange;
        this.constRange = new BigIntegerInterval(BigInteger.ZERO, constPosRange.subtract(constNegRange));
        this.constPosRange = new BigIntegerInterval(BigInteger.ZERO, constPosRange);
        if (Globals.useAssertions) {
            assert(coeffRange.signum() > 0);
            assert(constPosRange.signum() >= 0);
            assert(constNegRange.signum() <= 0);
            assert(constPosRange.compareTo(constNegRange) >= 0);
        }
        this.ranges = new LinkedHashMap<String, BigIntegerInterval>();
        this.memoryLeft = new HashMap<TRSTerm, VarPolynomial>();
        this.memoryRight = new HashMap<TRSTerm, VarPolynomial>();
        this.factory = new FullSharingFactory<Diophantine>();
        this.negRangeCriterion = negRangeCriterion;
        this.potentiallyNegativeSymbols = new LinkedHashSet<FunctionSymbol>();
        this.partialDioEval = partialDioEval;
    }

    /**
     * Converts a solution to the NegPolo ordering.
     * Note that up to now NegPolo only can represent linear polynomials.
     * => We will get undetected errors when calling this method for non-linear interpretations!
     * @param assignment
     * @return
     */
    private NegPolyOrder getSolution(Map<String, BigInteger> assignment) {
        Map<FunctionSymbol, int[]> solution = new LinkedHashMap<FunctionSymbol, int[]>(this.interpretation.size());
        for (Map.Entry<FunctionSymbol, VarPolynomial> fAndInter : this.interpretation.entrySet()) {
            FunctionSymbol f = fAndInter.getKey();
            final int n = f.getArity();
            VarPolynomial interpretation = fAndInter.getValue();
            int[] negPoloInter = new int[n+1];
            SimplePolynomial constant = interpretation.getConstantPart();
            BigInteger constantValue = constant.interpret(assignment, BigInteger.ZERO);
            if (Globals.useAssertions) {
                assert constantValue.compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) <= 0;
            }
            negPoloInter[0] = constantValue.intValue();
            for (int i=0; i<n; ) {
                SimplePolynomial coeff = interpretation.getCoefficientPoly(NegPoloInterpretation.VARIABLE_PREFIX+i);
                i++;
                BigInteger coeffValue = coeff.interpret(assignment, BigInteger.ZERO);
                if (Globals.useAssertions) {
                    assert coeffValue.compareTo(BigInteger.valueOf(Integer.MAX_VALUE)) <= 0;
                }
                negPoloInter[i] = coeffValue.intValue();
            }
            solution.put(f, negPoloInter);
        }
        return new NegPolyOrder(solution);
    }

    /**
     *
     * @param qdp
     * @param coeffRange
     * @param constPosRange
     * @param constNegRange
     * @param aborter
     * @return a Pair of
     *  - the solving NegPolyOrder
     *  - set of rules of R that are still to be considered given the
     *    implicit AFS induced by the NegPolyOrder
     *  or null if no such NegPolyOrder could be found
     */
    /*
    public static Pair<NegPolyOrder, Set<Rule>> solve(QDPProblem qdp, int coeffRange,
            int constPosRange, int constNegRange, SATCheckerFactory factory,
            Abortion aborter) throws AbortionException {

        Set<Rule> P = qdp.getP();
        Map<Rule, QActiveCondition> R = qdp.getQUsableRulesCalculator().getActiveConditions(P);
        NegPolyOrder npo = solve(P, R, coeffRange, constPosRange, constNegRange, factory, aborter);

        Set<Rule> filteredR = new LinkedHashSet<Rule>(R.size());
        for (Map.Entry<Rule, QActiveCondition> e : R.entrySet()) {
            QActiveCondition cond = e.getValue();
            if (npo.checkQActiveCondition(cond)) {
                filteredR.add(e.getKey());
            }
        }
        return new Pair<NegPolyOrder, Set<Rule>>(npo, filteredR);
    }
    */

    /**
     *
     * @param P
     * @param R
     * @param coeffRange
     * @param constPosRange
     * @param constNegRange
     * @param aborter
     * @return
     */
    public static NegPolyOrder solve(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R,
            BigInteger coeffRange, BigInteger constPosRange, BigInteger constNegRange, boolean allStrict,
            DiophantineSATConverter dioSatConv, SatEngine satEngine, NegRangeCriterion negRangeCriterion,
            boolean partialDioEval, Abortion aborter) throws AbortionException {

        NegPoloInterpretation interpretation = new NegPoloInterpretation(coeffRange,
                constPosRange, constNegRange, negRangeCriterion, partialDioEval);
        Pair<Map<String, BigIntegerInterval>, Formula<Diophantine>> diophantineProblem = interpretation.encode(P, R, allStrict, aborter);

        if (NegPoloInterpretation.log.isLoggable(Level.FINEST)) {
            NegPoloInterpretation.log.log(Level.FINEST, "Diophantine formula to be converted: " + diophantineProblem.y + "\n");
        }

        // solve the diophantineProblem
        Map<String, BigInteger> coeffRanges = new LinkedHashMap<String, BigInteger>(diophantineProblem.x.size());
        for (Map.Entry<String, BigIntegerInterval> e : diophantineProblem.x.entrySet()) {
            BigIntegerInterval ii = e.getValue();
            if (Globals.useAssertions) {
                assert ii.min.signum() == 0;
            }
            coeffRanges.put(e.getKey(), ii.max);
        }
        FormulaFactory<None> formulaFactory = satEngine.getFormulaFactory();
        PoloSatConverter converter = dioSatConv.getPoloSatConverter(formulaFactory,
                coeffRanges, coeffRange);

        SatSearch satSearcher = SatSearch.create(satEngine, converter);
        Map<String, BigInteger> solution = satSearcher.search(diophantineProblem.y, aborter);

        if (solution != null) {
            return interpretation.getSolution(solution);
        } else {
            return null;
        }
    }



    /**
     *
     * @param P
     * @param R
     * @param coeffRange
     * @param constPosRange
     * @param constNegRange
     * @param aborter
     * @return
     */
    public static Pair<NegPolyOrder,Set<Variable<AfsProp>>> solve(Set<Pair<TRSTerm,TRSTerm>> P,
            Collection<Pair<? extends GeneralizedRule, Variable<AfsProp>>> R,
            Formula<AfsProp> sideCondition,
            BigInteger coeffRange, BigInteger constPosRange, BigInteger constNegRange, boolean allStrict,
            DiophantineSATConverter dioSatConv, SatEngine satEngine,
            NegRangeCriterion negRangeCriterion,
            boolean partialDioEval,
            Abortion aborter) throws AbortionException {

        NegPoloInterpretation interpretation = new NegPoloInterpretation(coeffRange,
                constPosRange, constNegRange, negRangeCriterion, partialDioEval);
        Triple<Map<String, BigIntegerInterval>, Formula<Diophantine>, Map<Variable<AfsProp>,Variable<Diophantine>>> diophantineProblem;
        diophantineProblem = interpretation.encode(P, R, sideCondition, allStrict);
        Map<Variable<AfsProp>,Variable<Diophantine>> varMap1 = diophantineProblem.z;

        if (NegPoloInterpretation.log.isLoggable(Level.FINEST)) {
            NegPoloInterpretation.log.log(Level.FINEST, "Diophantine formula to be converted: " + diophantineProblem.y + "\n");
        }

        // solve the diophantineProblem
        Map<String, BigInteger> coeffRanges = new LinkedHashMap<String, BigInteger>(diophantineProblem.x.size());
        for (Map.Entry<String, BigIntegerInterval> e : diophantineProblem.x.entrySet()) {
            BigIntegerInterval ii = e.getValue();
            if (Globals.useAssertions) {
                assert ii.min.signum() == 0;
            }
            coeffRanges.put(e.getKey(), ii.max);
        }
        FormulaFactory<None> formulaFactory = satEngine.getFormulaFactory();
        PoloSatConverter converter = dioSatConv.getPoloSatConverter(formulaFactory,
                coeffRanges, coeffRange);

        SatSearch satSearcher = SatSearch.create(satEngine, converter);
        Set<Variable<Diophantine>> trueVars = new HashSet<Variable<Diophantine>>(varMap1.values());
        Map<String, BigInteger> solution = satSearcher.search(diophantineProblem.y, aborter, trueVars);

        if (solution != null) {
            Set<Variable<AfsProp>> interestingTrueVars = new HashSet<Variable<AfsProp>>();
            for (Pair<?,Variable<AfsProp>> rule : R) {
                Variable<Diophantine> dioVar = varMap1.get(rule.y);
                if (trueVars.contains(dioVar)) {
                    interestingTrueVars.add(rule.y);
                }
            }
            return new Pair<NegPolyOrder,Set<Variable<AfsProp>>>(interpretation.getSolution(solution), interestingTrueVars);
        } else {
            return null;
        }

    }

    private String getNextCoeff() {
        this.nextCoeff++;
        return NegPoloInterpretation.COEFF_PREFIX + this.nextCoeff;
    }


    /**
     * returns the (linear) interpretation for f.
     * can on demand create new interpretations.
     * Each interpretation for a n-ary f is a polynomial in
     * the variables x_0 to x_{n-1}, where x_ is the common variable prefix.
     * TODO: As soon as we allow non-linear interpretations we will have a problem
     * when using the current getSolution-method as NegPolo can only represent
     * linear interpretations.
     * @param f
     * @return
     */
    private VarPolynomial getInterpretation(FunctionSymbol f) {
        VarPolynomial p = this.interpretation.get(f);
        if (p == null) {
            int n = f.getArity();
            String coeff = this.getNextCoeff();
            p = VarPolynomial.createCoefficient(coeff);
            switch (this.negRangeCriterion) {
            case ALWAYS : {
                p = p.plus(VarPolynomial.create(this.constNegRange));
                this.ranges.put(coeff, this.constRange);
                break;
            }
            case NON_CONSTANTS : {
                if (n > 0) {
                    p = p.plus(VarPolynomial.create(this.constNegRange));
                    this.ranges.put(coeff, this.constRange);
                }
                else {
                    // max(0, c) is always 0 if c < 0, so only allow c >= 0
                    // for 0-ary function symbols to make the SAT instance
                    // smaller
                    this.ranges.put(coeff, this.constPosRange);
                }
                break;
            }
            case DAMPEN : {
                if (this.potentiallyNegativeSymbols.contains(f)) {
                    if (Globals.useAssertions) {
                        // constants never have function symbols below them
                        assert n > 0;
                    }
                    p = p.plus(VarPolynomial.create(this.constNegRange));
                    this.ranges.put(coeff, this.constRange);
                }
                else {
                    this.ranges.put(coeff, this.constPosRange);
                }
                break;
            }
            default :
                throw new RuntimeException("Unknown criterion for negative ranges: " +
                                                this.negRangeCriterion);
            }
            NegPoloInterpretation.log.config("Constant for " + f + ": " + p);
            for (int i=0; i<n; i++) {
                coeff = this.getNextCoeff();
                this.ranges.put(coeff, this.coeffRange);
                VarPolynomial addend = VarPolynomial.createVariable(NegPoloInterpretation.VARIABLE_PREFIX+i).times(SimplePolynomial.create(coeff));
                p = p.plus(addend);
            }
            this.interpretation.put(f, p);
        }
        return p;
    }


    private void computeRanges(Set<TRSTerm> rhss) {
        if (this.negRangeCriterion != NegRangeCriterion.DAMPEN) {
            return;
        }
        // f may get a negative constant if it is at the root of
        // a subterm u of t \in rhss such that u contains another symbol

        // temporary helper
        Set<FunctionSymbol> seenOnLeafPath = new LinkedHashSet<FunctionSymbol>();
        for (TRSTerm t : rhss) {
            Collection<Position> leafPositions = t.getLeafPositions();

            // check all the paths to the leaves:
            // if f occurs before g != f, then f is potentially negative
            for (Position pos : leafPositions) {
                ArrayList<FunctionSymbol> leafPath = t.getPathLabels(pos);
                // we add a symbol to potentiallyNegativeSymbols if it occurs in trace
                // and has a different symbol to its right
                for (int i = leafPath.size()-1; i >= 0; --i) {
                    FunctionSymbol f = leafPath.get(i);
                    seenOnLeafPath.add(f);
                    int seenOnLeafPathSize = seenOnLeafPath.size();
                    if (seenOnLeafPathSize >= 2) {
                        // we have seen at least 1 symbol on trace that is not f
                        this.potentiallyNegativeSymbols.add(f);
                    } /* else {
                        // there is only f in seenOnLeafPath,
                        // so no /other/ symbol below it; nothing to do
                    } */
                }
                seenOnLeafPath.clear();
            }
        }
    }

    /**
     * @param rules - {l_1 -> r_1, ..., l_n -> r_n}
     * @param rhss - non-null; gets r_1, ..., r_n added to it
     */
    private static void collectRhss(Collection<? extends GeneralizedRule> rules, Set<TRSTerm> rhss) {
        for (GeneralizedRule rule : rules) {
            rhss.add(rule.getRight());
        }
    }
    /**
     * encode a QActiveCondition into a formula
     * @param qac
     * @return
     */
    private Formula<Diophantine> encodeQActiveCondition(QActiveCondition qac) {
        Set<? extends Set<Pair<FunctionSymbol, Integer>>> activeCondition = qac.getSetRepresentation();
        ArrayList<Formula<Diophantine>> disjunction = new ArrayList<Formula<Diophantine>>(activeCondition.size());
        for (Set<Pair<FunctionSymbol, Integer>> conjunction : activeCondition) {
            ArrayList<Formula<Diophantine>> conjunctionList = new ArrayList<Formula<Diophantine>>(conjunction.size());
            for (Pair<FunctionSymbol, Integer> element : conjunction) {
                VarPolynomial interpretation = this.getInterpretation(element.x);
                int argument = element.y;
                SimplePolynomial coefficient = interpretation.getSumOfCoefficientPolys(NegPoloInterpretation.VARIABLE_PREFIX+argument);
                // TODO: maybe disjunction instead of sum
                Diophantine dio = Diophantine.create(coefficient, ConstraintType.GT);
                conjunctionList.add(this.factory.buildTheoryAtom(dio));
            }
            disjunction.add(this.factory.buildAnd(conjunctionList));
        }
        return this.factory.buildOr(disjunction);
    }

    private Formula<Diophantine> encodeAfsProp(Formula<AfsProp> formula, Map<Variable<AfsProp>,Variable<Diophantine>> varMap) {
        TheoryConverter<AfsProp, Diophantine> converter = new TheoryConverter<AfsProp, Diophantine>() {
            @Override
            public Formula<Diophantine> convert(AfsProp fi) {
                FunctionSymbol f = fi.f;
                int i = fi.i;
                VarPolynomial interpretation = NegPoloInterpretation.this.getInterpretation(f);
                SimplePolynomial coefficient = interpretation.getSumOfCoefficientPolys(NegPoloInterpretation.VARIABLE_PREFIX+i); // TODO check index shift
                Diophantine dio = Diophantine.create(coefficient, ConstraintType.GT);
                return NegPoloInterpretation.this.factory.buildTheoryAtom(dio);
            }
        };


        TheoryConverterVisitor<AfsProp, Diophantine> visitor;
        visitor = new TheoryConverterVisitor<AfsProp, Diophantine>(this.factory, converter, varMap);

        return formula.apply(visitor);
    }



    /**
     * encodes the (active) constraints that arise for the DP-Problem into a diophantine SPC-formula.
     * Moreover, the ranges for all coefficients in the SPC-formula are given and all these
     * ranges are intervals from 0 to some arbitrary natural number.
     * @param P
     * @param R - usually the usable rules with active conditions
     * @param allStrict
     * @return
     */
    private Pair<Map<String, BigIntegerInterval>, Formula<Diophantine>> encode(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R, boolean allStrict,
            Abortion aborter) throws AbortionException {
        final Set<TRSTerm> rhss = new LinkedHashSet<TRSTerm>();
        NegPoloInterpretation.collectRhss(P, rhss);
        NegPoloInterpretation.collectRhss(R.keySet(), rhss);
        this.computeRanges(rhss);
        this.encode(R, aborter);
        Set<SimplePolynomial> greaterConditions = new LinkedHashSet<SimplePolynomial>(P.size());
        for (GeneralizedRule rule : P) {
            aborter.checkAbortion();
            VarPolynomial left = this.interpret(rule.getLhsInStandardRepresentation(), true, this.memoryLeft);
            aborter.checkAbortion();
            VarPolynomial right = this.interpret(rule.getRhsInStandardRepresentation(), false, this.memoryRight);
            aborter.checkAbortion();
            VarPolynomial difference = left.minus(right);
            for (SimplePolynomial simplePoly : difference.getCoefficientsOfVariables()) {
                Diophantine dio = Diophantine.create(simplePoly, ConstraintType.GE);
                this.sideConditions.add(this.factory.buildTheoryAtom(dio));
            }
            greaterConditions.add(difference.getConstantPart());

        }
        aborter.checkAbortion();

        if (allStrict) {
            for (SimplePolynomial greater : greaterConditions) {
                Diophantine dio = Diophantine.create(greater, ConstraintType.GT);
                this.sideConditions.add(this.factory.buildTheoryAtom(dio));
            }
        } else {
            List<Formula<Diophantine>> eqConstraints = new ArrayList<Formula<Diophantine>>(greaterConditions.size());
            for (SimplePolynomial greater : greaterConditions) {
                Pair<SimplePolynomial, SimplePolynomial> leftAndRight;
                leftAndRight = greater.toPositivePair();
                Diophantine dioGe, dioEq;
                dioGe = Diophantine.create(leftAndRight.x, leftAndRight.y, ConstraintType.GE);
                dioEq = Diophantine.create(leftAndRight.x, leftAndRight.y, ConstraintType.EQ);
                this.sideConditions.add(this.factory.buildTheoryAtom(dioGe));
                eqConstraints.add(this.factory.buildTheoryAtom(dioEq));
            }
            this.sideConditions.add(this.factory.buildNot(this.factory.buildAnd(eqConstraints)));
        }
        aborter.checkAbortion();

        Formula<Diophantine> finalFormula = this.factory.buildAnd(this.sideConditions);
        return new Pair<Map<String, BigIntegerInterval>, Formula<Diophantine>>(this.ranges, finalFormula);

    }

    /**
     * encodes the (active) constraints that arise for the DP-Problem into a diophantine SPC-formula.
     * Moreover, the ranges for all coefficients in the SPC-formula are given and all these
     * ranges are intervals from 0 to some arbitrary natural number.
     * @param P
     * @param R - usually the usable rules with active conditions
     * @param allStrict
     * @return
     */
    private Triple<Map<String, BigIntegerInterval>, Formula<Diophantine>, Map<Variable<AfsProp>,Variable<Diophantine>>> encode(
            Set<Pair<TRSTerm,TRSTerm>> P,
            Collection<Pair<? extends GeneralizedRule, Variable<AfsProp>>> R,
            Formula<AfsProp> sideCondition,
            boolean allStrict) {
        final Set<TRSTerm> rhss = NegPoloInterpretation.getRhss(P, R);
        this.computeRanges(rhss);
        Map<Variable<AfsProp>, Variable<Diophantine>> varMapping = new HashMap<Variable<AfsProp>, Variable<Diophantine>>();
        this.encode(R, varMapping);
        Set<SimplePolynomial> greaterConditions = new LinkedHashSet<SimplePolynomial>(P.size());
        for (Pair<TRSTerm,TRSTerm> rule : P) {
            VarPolynomial left = this.interpret(rule.x, true, this.memoryLeft);
            VarPolynomial right = this.interpret(rule.y, false, this.memoryRight);
            VarPolynomial difference = left.minus(right);

            for (SimplePolynomial simplePoly : difference.getCoefficientsOfVariables()) {
                Diophantine dio = Diophantine.create(simplePoly, ConstraintType.GE);
                this.sideConditions.add(this.factory.buildTheoryAtom(dio));
            }
            greaterConditions.add(difference.getConstantPart());
        }


        if (allStrict) {
            for (SimplePolynomial greater : greaterConditions) {
                Diophantine dio = Diophantine.create(greater, ConstraintType.GT);
                this.sideConditions.add(this.factory.buildTheoryAtom(dio));
            }
        } else {
            List<Formula<Diophantine>> eqConstraints = new ArrayList<Formula<Diophantine>>(greaterConditions.size());
            for (SimplePolynomial greater : greaterConditions) {
                Pair<SimplePolynomial, SimplePolynomial> leftAndRight;
                leftAndRight = greater.toPositivePair();
                Diophantine dioGe, dioEq;
                dioGe = Diophantine.create(leftAndRight.x, leftAndRight.y, ConstraintType.GE);
                dioEq = Diophantine.create(leftAndRight.x, leftAndRight.y, ConstraintType.EQ);
                this.sideConditions.add(this.factory.buildTheoryAtom(dioGe));
                eqConstraints.add(this.factory.buildTheoryAtom(dioEq));
            }
            this.sideConditions.add(this.factory.buildNot(this.factory.buildAnd(eqConstraints)));
        }

        this.sideConditions.add(this.encodeAfsProp(sideCondition, varMapping));

        Formula<Diophantine> finalFormula = this.factory.buildAnd(this.sideConditions);

        Map<Variable<AfsProp>, Variable<Diophantine>> requiredVarMapping;
        if (varMapping.size() > 2*R.size()) {
            requiredVarMapping = new HashMap<Variable<AfsProp>, Variable<Diophantine>>(R.size());
            for (Pair<?,Variable<AfsProp>> rule : R) {
                requiredVarMapping.put(rule.y, varMapping.get(rule.y));
            }
        } else {
            requiredVarMapping = varMapping;
        }

        return new Triple<Map<String, BigIntegerInterval>, Formula<Diophantine>, Map<Variable<AfsProp>, Variable<Diophantine>>>(this.ranges, finalFormula, requiredVarMapping);
    }

    /**
     * @param P
     * @param R
     * @return the right-hand sides of the term pairs in P and R
     */
    private static Set<TRSTerm> getRhss(Set<Pair<TRSTerm,TRSTerm>> P,
            Collection<Pair<? extends GeneralizedRule, Variable<AfsProp>>> R) {
        Set<TRSTerm> res = new LinkedHashSet<TRSTerm>();
        for (Pair<TRSTerm, TRSTerm> st : P) {
            res.add(st.y);
        }
        for (Pair<? extends GeneralizedRule, Variable<AfsProp>> stv : R) {
            res.add(stv.x.getRight());
        }
        return res;
    }



    /**
     * require that (l >= r if condition) is satisfied
     * @param condition
     * @param rule
     */
    private void encode(Map<? extends GeneralizedRule, QActiveCondition> R, Abortion aborter)
            throws AbortionException {
        aborter.checkAbortion();
        for (Map.Entry<? extends GeneralizedRule, QActiveCondition> qRule : R.entrySet()) {
            GeneralizedRule rule = qRule.getKey();
            Formula<Diophantine> condition = this.encodeQActiveCondition(qRule.getValue());
            aborter.checkAbortion();
            VarPolynomial left = this.interpret(rule.getLhsInStandardRepresentation(), true, this.memoryLeft);
            aborter.checkAbortion();
            VarPolynomial right = this.interpret(rule.getRhsInStandardRepresentation(), false, this.memoryRight);
            aborter.checkAbortion();
            VarPolynomial difference = left.minus(right);
            Collection<SimplePolynomial> coeffs = difference.getCoefficientsOfVariables();

            ArrayList<Formula<Diophantine>> andConditions = new ArrayList<Formula<Diophantine>>(coeffs.size()+1);
            for (SimplePolynomial simplePoly : coeffs) {
                Diophantine dio = Diophantine.create(simplePoly, ConstraintType.GE);
                andConditions.add(this.factory.buildTheoryAtom(dio));
            }
            Diophantine dio = Diophantine.create(difference.getConstantPart(), ConstraintType.GE);
            andConditions.add(this.factory.buildTheoryAtom(dio));

            Formula<Diophantine> requirement = this.factory.buildAnd(andConditions);
            requirement = this.factory.buildOr(this.factory.buildNot(condition), requirement);

            this.sideConditions.add(requirement);
        }
        aborter.checkAbortion();
    }

    /**
     * require that l >= r if usable variable is true
     * @param condition
     * @param rule
     */
    private void encode(Collection<Pair<? extends GeneralizedRule, Variable<AfsProp>>> R,
            Map<Variable<AfsProp>,Variable<Diophantine>> varMap) {
        for (Pair<? extends GeneralizedRule, Variable<AfsProp>> qRule : R) {
            GeneralizedRule rule = qRule.x;
            Variable<Diophantine> condition = varMap.get(qRule.y);
            if (condition == null) {
                condition = this.factory.buildVariable();
                varMap.put(qRule.y, condition);
            }
            VarPolynomial left = this.interpret(rule.getLhsInStandardRepresentation(), true, this.memoryLeft);
            VarPolynomial right = this.interpret(rule.getRhsInStandardRepresentation(), false, this.memoryRight);
            VarPolynomial difference = left.minus(right);
            Collection<SimplePolynomial> coeffs = difference.getCoefficientsOfVariables();

            ArrayList<Formula<Diophantine>> andConditions = new ArrayList<Formula<Diophantine>>(coeffs.size()+1);
            for (SimplePolynomial simplePoly : coeffs) {
                Diophantine dio = Diophantine.create(simplePoly, ConstraintType.GE);
                andConditions.add(this.factory.buildTheoryAtom(dio));
            }
            Diophantine dio = Diophantine.create(difference.getConstantPart(), ConstraintType.GE);
            andConditions.add(this.factory.buildTheoryAtom(dio));

            Formula<Diophantine> requirement = this.factory.buildAnd(andConditions);
            requirement = this.factory.buildOr(this.factory.buildNot(condition), requirement);

            this.sideConditions.add(requirement);
        }
    }



    /**
     * Interprets a term t with Pleft or Pright, depending on the left flag.
     * All the side-conditions to compute Pleft/right are stored internally.
     * (The side-conditions are the formulae alpha in the paper.)
     * @param t
     * @param left
     * @param memory
     * @return
     */
    private VarPolynomial interpret(TRSTerm t, boolean left, Map<TRSTerm, VarPolynomial> memory) {
        final VarPolynomial result = memory.get(t);
        final VarPolynomial res;
        if (result == null) {
            if (t.isVariable()) {
                res = VarPolynomial.createVariable(((aprove.verification.dpframework.BasicStructures.TRSVariable) t).getName());
            } else {
                TRSFunctionApplication ft = (TRSFunctionApplication) t;
                FunctionSymbol f = ft.getRootSymbol();
                int n = f.getArity();
                VarPolynomial p0 = this.getInterpretation(f);
                Map<String, VarPolynomial> substitution = new LinkedHashMap<String, VarPolynomial>(2*n);
                int i = 0;
                for (TRSTerm arg : ft.getArguments()) {
                    substitution.put(NegPoloInterpretation.VARIABLE_PREFIX+i, this.interpret(arg, left, memory));
                    i++;
                }
                VarPolynomial p = p0.substituteVariables(substitution);
                // at this point p contains f_Z

                if (this.partialDioEval && p0.getConstantPart().allPositive()) {
                    // Nice, f for sure does not have a negative constant,
                    // so we need no new coefficient b_t^left and no side
                    // constraints -- the result is simply p.
                    res = p;
                }
                else if (left) {
                    SimplePolynomial Q = p.getConstantPart();
                    BigInteger min = Q.min(this.ranges);
                    BigInteger max = Q.max(this.ranges);
                    if (min.signum() > 0) {
                        min = BigInteger.ZERO;
                    }
                    if (max.signum() < 0) {
                        max = BigInteger.ZERO;
                    }
                    String coeff = this.getNextCoeff();
                    BigInteger maxMinusMin = max.subtract(min);
                    if (Globals.useAssertions) {
                        assert maxMinusMin.signum() > 0 :
                            "maxMinusMin = " + maxMinusMin +
                            ", but should be > 0\nconstant part: " + Q +
                            "\nmin: " + Q.min(this.ranges) +
                            "\nmax: " + Q.max(this.ranges) +
                            "\nranges: " + this.ranges;
                    }

                    this.ranges.put(coeff, new BigIntegerInterval(BigInteger.ZERO, maxMinusMin));
                    SimplePolynomial a_t = SimplePolynomial.create(coeff).plus(SimplePolynomial.create(min));
                    res = p.plus(VarPolynomial.create(a_t).minus(VarPolynomial.create(Q)));

                    Set<SimplePolynomial> q_i_s = p.getCoefficientsOfVariables();
                    ArrayList<Formula<Diophantine>> conditions = new ArrayList<Formula<Diophantine>>(q_i_s.size()+1);
                    for (SimplePolynomial q_i : q_i_s) {
                        Diophantine dio = Diophantine.create(q_i, ConstraintType.EQ);
                        conditions.add(this.factory.buildTheoryAtom(dio));
                    }
                    Diophantine dio = Diophantine.create(Q.negate(), ConstraintType.GT);
                    conditions.add(this.factory.buildTheoryAtom(dio));

                    Formula<Diophantine> condition = this.factory.buildAnd(conditions);
                    this.addConditionalAssignment(a_t, condition, SimplePolynomial.ZERO, Q, this.sideConditions);

                } else {
                    // in the right case we only look at the constant
                    SimplePolynomial Q = p.getConstantPart();
                    BigInteger min = Q.min(this.ranges);
                    if (min.signum() < 0) {
                        min = BigInteger.ZERO;
                    }
                    BigInteger max = Q.max(this.ranges);
                    if (max.signum() < 0) {
                        max = BigInteger.ZERO;
                    }
                    // so we do not know in which case we are
                    String coeff = this.getNextCoeff();
                    BigInteger maxMinusMin = max.subtract(min);
                    if (Globals.useAssertions) {
                        assert maxMinusMin.signum() > 0 :
                            "maxMinusMin = " + maxMinusMin +
                            ", but should be > 0\nconstant part: " + Q +
                            "\nmin: " + Q.min(this.ranges) +
                            "\nmax: " + Q.max(this.ranges) +
                            "\nranges: " + this.ranges;
                    }
                    this.ranges.put(coeff, new BigIntegerInterval(BigInteger.ZERO, maxMinusMin));
                    SimplePolynomial a_t = SimplePolynomial.create(coeff).plus(SimplePolynomial.create(min));
                    res = p.plus(VarPolynomial.create(a_t).minus(VarPolynomial.create(Q)));

                    Diophantine dio = Diophantine.create(Q, ConstraintType.GE);
                    Formula<Diophantine> condition = this.factory.buildTheoryAtom(dio);
                    this.addConditionalAssignment(a_t, condition, Q, SimplePolynomial.ZERO, this.sideConditions);
                }
            }
            memory.put(t, res);
        } else {
            // we use the memory
            res = result;
        }
        return res;
    }

    /**
     * Adds two Diophantine Formulae to <code>constraints</code> that amount to:
     *   *  (condition -> x = thenValue)
     *   *  ((not condition) -> x = elseValue)
     *
     * In Java:   x = condition ? thenValue : elseValue
     *
     * @param x
     * @param condition
     * @param thenValue
     * @param elseValue
     * @param constraints
     */
    private void addConditionalAssignment(SimplePolynomial x, Formula<Diophantine> condition,
            SimplePolynomial thenValue, SimplePolynomial elseValue, Collection<Formula<Diophantine>> constraints) {
        SimplePolynomial thenPoly = x.minus(thenValue);
        SimplePolynomial elsePoly = x.minus(elseValue);

        Diophantine dioThen = Diophantine.create(thenPoly, ConstraintType.EQ);
        Diophantine dioElse = Diophantine.create(elsePoly, ConstraintType.EQ);

        Formula<Diophantine> thenFormula = this.factory.buildTheoryAtom(dioThen);
        Formula<Diophantine> elseFormula = this.factory.buildTheoryAtom(dioElse);

        // the following line can be used instead of the two disjunctions,
        // but MiniSAT does not like it as much as one might think
        //constraints.add(this.factory.buildIte(condition, thenFormula, elseFormula));
        constraints.add(this.factory.buildOr(this.factory.buildNot(condition), thenFormula));
        constraints.add(this.factory.buildOr(condition, elseFormula));
    }

}


