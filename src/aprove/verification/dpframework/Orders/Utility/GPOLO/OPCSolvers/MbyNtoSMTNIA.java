package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SMTSearch.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This implementation of OPCSolver transforms the OPC to SimplePolyConstraints
 * and uses some (already existing) solver to handle these constraints.
 * The constraints must be built using MbyN coefficients.
 * @author ckuknat
 */
public class MbyNtoSMTNIA implements OPCSolver<MbyN> {
    /**
     * The polynomial ring.
     */
    private Ring<GPoly<MbyN, GPolyVar>> polyRing;

    /**
     * The flattening visitor for coefficient polynomials.
     */
    private FlatteningVisitor<MbyN, GPolyVar> fvInner;

    /**
     * The flattening visitor for order polynomials.
     */
    private FlatteningVisitor<GPoly<MbyN, GPolyVar>, GPolyVar> fvOuter;

    /**
     * If this variable is set all denominators will be set to the maximal
     * value that the denominators' range allows.
     */
    private final boolean denomFixed;

    public static long encodeTime;
    public static long solveTime;
    public static long decodeTime;

    @ParamsViaArgumentObject
    public MbyNtoSMTNIA(final Arguments arguments) {
        this.denomFixed = arguments.fixDenominator;
        this.smtEngine = arguments.smtEngine;
    }

    /**
     * For directly searching on rational constraints we us ratSearch and
     * therefore have the engine and the string format at this place
     */

    private final SMTEngine smtEngine;

    /**
     * This constructor should get used in SMTEngine
     *
     * @param converter
     *            The correct converter to handle the rational constraints
     * @param smtEngine
     *            The Engine has solving abilities
     * @param denomFixed
     *            Choose between some variants of searching
     */
    public MbyNtoSMTNIA(final MbyNSMTConverter converter, final SMTEngine smtEngine, final boolean denomFixed) {
        this.smtEngine = smtEngine;
        this.denomFixed = denomFixed;
        // We don't need a solver as we search for the solution by ourselves
    }

    /**
     * Solve the given constraint (encapsulating the single constraints).
     * @param constraint Some OrderPolyConstraint that should be solved.
     * @param ranges The range for the variables.
     * @param defaultRange The range for the variables not mentioned in ranges.
     * @return A value for every variable.
     * @param aborter Some aborter.
     * @throws AbortionException when the aborter kicks in.
     */
    @Override
    public Map<GPolyVar, MbyN> solve(final OrderPolyConstraint<MbyN> constraint,
        final Map<GPolyVar, OPCRange<MbyN>> ranges,
        final OPCRange<MbyN> defaultRange,
        final Abortion aborter) throws AbortionException {

        BigInteger denominator = null;
        if (this.denomFixed) {
            denominator = defaultRange.getList().get(0).y.getNumerator();
        }
        final VariableConverterMbyN varConv = new VariableConverterMbyN(denominator);
        assert (varConv != null);
        final Ring<MbyN> innerRing = (Ring<MbyN>) this.fvInner.getRingC();
        final MbyNExtractFormulaVisitor cv =
            new MbyNExtractFormulaVisitor(innerRing, this.polyRing, this.fvInner.getMonoid(), this.fvInner,
                this.fvOuter, ranges, varConv, defaultRange, denominator);
        cv.applyToWithCleanup(constraint);

        final Formula<Diophantine> formula = cv.getFormula();
        if (Globals.useAssertions) {
            assert (defaultRange.getList() != null && defaultRange.getList().size() == 1);
        }
        final FormulaToSPCsVisitor formulaToSPCs = new FormulaToSPCsVisitor();

        formula.apply(formulaToSPCs);
        final Pair<Set<SimplePolyConstraint>, Set<SimplePolyConstraint>> spcs = formulaToSPCs.getPair();
        final Set<String> variables = formulaToSPCs.getVariables();
        final List<SMTLIBTheoryAtom> spcList = new LinkedList<>();
        for (final SimplePolyConstraint spc : spcs.x) {
            spcList.add(spc.toSMTLIB());
        }
        for (final SimplePolyConstraint strictSpc : spcs.y) {
            spcList.add(strictSpc.toSMTLIB());
        }

        final FormulaFactory<SMTLIBTheoryAtom> factory = new AtomCachingFactory<>();
        final List<TheoryAtom<SMTLIBTheoryAtom>> atomList = factory.buildTheoryAtoms(spcList);

        final SMTLIBIntConstant zero = SMTLIBIntConstant.create(BigInteger.ZERO);
        final Map<String, BigInteger> integerRanges = cv.getRanges();
        for (final String var : variables) {
            // var >= 0
            final SMTLIBIntVariable smtVar = SMTLIBIntVariable.create(var);
            final SMTLIBIntGE lowerConstraint = SMTLIBIntGE.create(smtVar, zero);
            atomList.add(factory.buildTheoryAtom(lowerConstraint));

            // var <= range
            final BigInteger range = integerRanges.get(var);
            if (range.compareTo(BigInteger.ZERO) >= 0) {
                final SMTLIBIntConstant smtRange = SMTLIBIntConstant.create(range);
                final SMTLIBIntGE upperConstraitn = SMTLIBIntGE.create(smtRange, smtVar);
                atomList.add(factory.buildTheoryAtom(upperConstraitn));

            }
        }
        final Formula<SMTLIBTheoryAtom> smtFormula = factory.buildAnd(atomList);

        Map<GPolyVar, BigInteger> solution = null;
        final List<Formula<SMTLIBTheoryAtom>> smtFormulaAsSingletonList = Collections.singletonList(smtFormula);
        Pair<YNM, Map<String, String>> r;
        try {
            r = this.smtEngine.solve(smtFormulaAsSingletonList, SMTLogic.QF_NIA, aborter);
        } catch (final WrongLogicException e) {
            // we do not care
            r = new Pair<>(YNM.MAYBE, null);
        }
        if (r.x == YNM.YES) {
            solution = new LinkedHashMap<>();
            for (final Map.Entry<String, String> assignment : r.y.entrySet()) {
                final GPolyVar variable = GAtomicVar.createVariable(assignment.getKey());
                final BigInteger value = new BigInteger(assignment.getValue());
                solution.put(variable, value);
            }
            varConv.setSolution(solution);
            varConv.setNumeratorsAndDenominators(cv.getNumerators(), cv.getDenominators());
            return varConv.getMap();
        }
        return null;
    }

    @Override
    public Map<GPolyVar, MbyN> solve(final OrderPolyConstraint<MbyN> constraint,
        final Domain domain,
        final Abortion aborter) throws AbortionException {
        throw new UnsupportedOperationException();
    }

    /**
     * @param polyRingParam the polynomial ring.
     */
    @Override
    public void setPolyRing(final Ring<GPoly<MbyN, GPolyVar>> polyRingParam) {
        this.polyRing = polyRingParam;
    }

    /**
     * @param inner the flattening visitor for coefficient polynomials.
     */
    @Override
    public void setFvInner(final FlatteningVisitor<MbyN, GPolyVar> inner) {
        this.fvInner = inner;
    }

    /**
     * @param outer the flattening visitor for order polynomials.
     */
    @Override
    public void setFvOuter(final FlatteningVisitor<GPoly<MbyN, GPolyVar>, GPolyVar> outer) {
        this.fvOuter = outer;
    }

    /**
     * @return whether the denominator is fixed or not
     */
    public boolean getDenomFixed() {
        return this.denomFixed;
    }

    @Override
    public OPCSolver<MbyN> getCopy() {
        final Arguments arguments = new Arguments();
        arguments.fixDenominator = this.denomFixed;
        final MbyNtoSMTNIA copy = new MbyNtoSMTNIA(arguments);
        copy.polyRing = this.polyRing;
        return copy;
    }

    public static class Arguments {
        /**
         * The engine which has to solve lra constraints
         */
        public SMTEngine smtEngine = new SMTLIBEngine();

        /**
         *  Fix the denominator to the maximal value of its range
         */
        public boolean fixDenominator = false;
    }

}
