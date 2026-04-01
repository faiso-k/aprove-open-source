/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SMTSearch.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.FullSharingFactory;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This implementation of OPCSolver transforms the OPC to SimplePolyConstraints
 * and uses some (already existing) solver to handle these constraints.
 * The constraints must be built using MbyN coefficients.
 * @author cotto
 */
public class MbyNtoSMTLRA implements OPCSolver<MbyN> {
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
    private FlatteningVisitor<GPoly<MbyN, GPolyVar>, GPolyVar>
        fvOuter;

    /**
     * If this variable is set all denominators will be set to the maximal
     * value that the denominators' range allows.
     */
    private final boolean denomFixed;

    private static final Logger log = Logger
            .getLogger("aprove.verification.dpframework/Orders/Utility/GPOLO/OPCSolvers/MbyNtoFormula");

    public static long encodeTime;
    public static long solveTime;
    public static long decodeTime;

    @ParamsViaArgumentObject
    public MbyNtoSMTLRA(Arguments arguments) {
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
    public MbyNtoSMTLRA(MbyNSMTConverter converter, SMTEngine smtEngine,
            boolean denomFixed) {
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
    public Map<GPolyVar, MbyN> solve(
            final OrderPolyConstraint<MbyN> constraint,
            final Map<GPolyVar, OPCRange<MbyN>> ranges,
            final OPCRange<MbyN> defaultRange,
            final Abortion aborter) throws AbortionException {
        throw new UnsupportedOperationException();
    }

    @Override
    public Map<GPolyVar, MbyN> solve(OrderPolyConstraint<MbyN> constraint,
            Domain domain, Abortion aborter) throws AbortionException {
        Ring<MbyN> innerRing = (Ring<MbyN>) this.fvInner.getRingC();
        final boolean flattenInner = false;

        MbyNExtractRatFormulaVisitor cv = new MbyNExtractRatFormulaVisitor(
                innerRing, this.polyRing, this.fvInner.getMonoid(),
                this.fvInner, this.fvOuter, flattenInner);
        cv.applyToWithCleanup(constraint);
        Set<GPolyVar> allVariables = cv.getVariables();
        // Here the constraint should be flat by now

        final Formula<OPCAtom<MbyN>> formula = cv.getFormula();

        FormulaToOPCsVisitor formulaToOPCs = new FormulaToOPCsVisitor();
        formula.apply(formulaToOPCs);
        // These are the constraints in relation to zero
        Pair<Set<OPCAtom<MbyN>>, Set<OPCAtom<MbyN>>> opcs = formulaToOPCs
                .getPair();
        Map<String, MbyN> solution = null;
        if (opcs != null) {
            if (domain != null) {
                solution = this.search(opcs.x, opcs.y, domain, aborter);
            }
        }

        if (solution != null) {
            Map<GPolyVar, MbyN> result = new LinkedHashMap<GPolyVar, MbyN>();
            for (Map.Entry<String, MbyN> entry : solution.entrySet()) {
                MbyN mbyn = entry.getValue();
                result.put(GAtomicVar.createVariable(entry.getKey()), mbyn);
            }
            // This has to happen if something like x-x while flattening has
            // been done
            for (GPolyVar var : allVariables) {
                if (!result.containsKey(var)) {
                    result.put(var, MbyN.create(BigInteger.ZERO));
                }
            }
            return result;
        } else {
            return null;
        }
    }

    /**
     * @param polyRingParam the polynomial ring.
     */
    @Override
    public void setPolyRing(
            final Ring<GPoly<MbyN, GPolyVar>> polyRingParam) {
        this.polyRing = polyRingParam;
    }

    /**
     * @param inner the flattening visitor for coefficient polynomials.
     */
    @Override
    public void setFvInner(
            final FlatteningVisitor<MbyN, GPolyVar> inner) {
        this.fvInner = inner;
    }

    /**
     * @param outer the flattening visitor for order polynomials.
     */
    @Override
    public void setFvOuter(
            final FlatteningVisitor<GPoly<MbyN, GPolyVar>, GPolyVar>
                outer) {
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
        Arguments arguments = new Arguments();
        arguments.fixDenominator = this.denomFixed;
        MbyNtoSMTLRA copy = new MbyNtoSMTLRA(arguments);
        copy.polyRing = this.polyRing;
        return copy;
    }

    public static class Arguments {
        /**
         * The engine which has to solve lra constraints
         */
        public SMTEngine smtEngine = new YicesEngine();

        /**
         *  Fix the denominator to the maximal value of its range
         */
        public boolean fixDenominator = false;
    }

    private Map<String, MbyN> search(Set<OPCAtom<MbyN>> constraints,
            Set<OPCAtom<MbyN>> strictConstraints, Domain domain,
            Abortion aborter) throws AbortionException {
        long l1, l2;

        // from here we have to convert the constraints into linear ones
        // we guaruanteed absolut positivness ... I hope
        // we flatened the outer polynomials ... I Guess
        // we only have to consider the left side ... I think
        // Now we should convert each OPCAtom<Mby> into a formula of linear
        // SMTConstraints

        FormulaFactory<SMTLIBTheoryAtom> factory;
        factory = new FullSharingFactory<SMTLIBTheoryAtom>();

        GPolyFactory<MbyN, GPolyVar> gPolyCoeffFactory = new aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.FullSharingFactory<MbyN, GPolyVar>();
        GPolyFactory<GPoly<MbyN, GPolyVar>, GPolyVar> gPolyCoeffFactory2 = new aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.FullSharingFactory<GPoly<MbyN, GPolyVar>, GPolyVar>();
        OrderPolyFactory<MbyN> orderPolyFactory = new OrderPolyFactory<MbyN>(
                gPolyCoeffFactory2, gPolyCoeffFactory);

        MbyNSMTConverter converter = new MbyNSMTConverter(factory, domain,
                this.fvOuter);
        converter.setRings(this.polyRing, (Ring<MbyN>) this.fvInner.getRingC(),
                this.fvInner.getMonoid());


        OPCtoRatFormulaVisitor<MbyN, SMTLIBTheoryAtom> toRatVisitor;
        toRatVisitor = new OPCtoRatFormulaVisitor<MbyN, SMTLIBTheoryAtom>(
                converter, orderPolyFactory, factory);

        l1 = System.nanoTime();

        List<Formula<SMTLIBTheoryAtom>> formulas = new LinkedList<Formula<SMTLIBTheoryAtom>>();
        // Aim is having much assertions here eventually... I think

        for (OPCAtom<MbyN> constraint : constraints) {
            this.fvOuter.applyTo(constraint.getLeftPoly());
            toRatVisitor.applyTo(constraint);
            Formula<SMTLIBTheoryAtom> formula = toRatVisitor.getFormula();
            formulas.add(formula);
        }
        for (OPCAtom<MbyN> strictConstraint : strictConstraints) {
            this.fvOuter.applyTo(strictConstraint.getLeftPoly());
            toRatVisitor.applyTo((OrderPolyConstraint<MbyN>) strictConstraint);
            Formula<SMTLIBTheoryAtom> formula = toRatVisitor.getFormula();
            formulas.add(factory.buildNot(formula));
        }


        l2 = System.nanoTime();
        MbyNtoSMTLRA.encodeTime = l2 - l1;
        if (MbyNtoSMTLRA.log.isLoggable(Level.FINER)) {
            MbyNtoSMTLRA.log
                    .log(
                            Level.FINER,
                            "Conversion and linearization via Integer Intervals of Formula<Diophantine> "
                                    + "with SimplePolynomial to Formula<SMTLIBIntCMP> took {0} ms.\n",
                            (MbyNtoSMTLRA.encodeTime / 1000000));
        }
        // System.out.println("Time (ms) for constraints to Prop Logic: "
        // + (l2 - l1) / 1000000 + "ms");

        aborter.checkAbortion();

        l1 = System.nanoTime();
        Pair<YNM, Map<String, String>> salvation;
        try {
            salvation = this.smtEngine.solve(formulas, SMTLogic.QF_LRA, aborter);
        } catch (final WrongLogicException e) {
            System.err.println("Solver error: " + e.getErrorMessage());
            salvation = new Pair<>(YNM.MAYBE, null);
        }
        final YNM success = salvation.x;
        final Map<String, String> results = salvation.y;

        l2 = System.nanoTime();
        MbyNtoSMTLRA.encodeTime = l2 - l1;
        // System.out.println("Time (ms) for Prop Logic to Rat model:   "
        // + (l2 - l1) / 1000000 + "ms");
        MbyNtoSMTLRA.solveTime = l2 - l1;
        if (success == YNM.MAYBE || results == null) {
            MbyNtoSMTLRA.decodeTime = 0;
            return null;
        }

        Map<String, MbyN> solution = new LinkedHashMap<String, MbyN>();
        for (Map.Entry<String, String> var : results.entrySet()) {
            solution.put(var.getKey(), MbyN.create(var.getValue()));
        }
        // for (SMTLIBRatVariable var : converter.getVariableMap().values()) {
        // solution.put(var.getName(), var.getResultAsMbyN());
        // }

        return solution;

    }

}
