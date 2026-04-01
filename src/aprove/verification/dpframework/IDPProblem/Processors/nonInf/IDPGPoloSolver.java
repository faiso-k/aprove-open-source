/**
 * Find a POLO using general polynomials over integers.
 * Stolen from {@link GPoloNatSolver} and adapted to integers.
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.nonInf;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.solver.*;
import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.orders.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.IConstraintGenerator.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.IDPGInterpretation.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.LogOPCSolver.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Monoids.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


public class IDPGPoloSolver
    implements IdpIUsableSolver {

    private static Logger log = Logger.getLogger("prove.DPFramework.IDPProblem.Processors.nonInf.IDPGPoloIntSolver");

    /**
     * The strict mode used here.
     */
    private final StrictMode strictMode;

    /**
     * The form of the to-be-constructed polynomials.
     */
    private final GInterpretationMode<BigIntImmutable> form;

    /**
     * The default range for the variables.
     */
    private final OPCRange<BigIntImmutable> range;

    /**
     * Generator for the pRules- and useableRules-contraints
     */
    private final IConstraintGenerator contraintGenerator;

    private final boolean isNat;
    private final boolean isTupleNat;

    private final IdpShapeHeuristic poloShapeHeuristic;

    private final LogOPCSolverFactory<BigIntImmutable> logOPCSolverFactory;

    @ParamsViaArgumentObject
    public IDPGPoloSolver (final Arguments arguments) {
        this(
                arguments.nat,
                arguments.natTuple,
                GInterpretationMode.<BigIntImmutable>createFromLegacy(
                        arguments.degree,
                        arguments.maxSimpleDegree < 0 ? Integer.MAX_VALUE : arguments.maxSimpleDegree),
                arguments.range,
                arguments.poloShapeHeuristic ,
                arguments.strictMode,
                arguments.constraintGenerator,
                arguments.opcSolver
        );
    }

    /**
     * Create the solver based on the given parameters.
     * @param form The form of the polynomials as specified in the
     * strategy.
     * @param idpShapeHeuristic
     * @param rangeParam The range of the variables.
     * @param strictModeParam The strict mode that should be used.
     * @param logOPCSolverFactory The solver that is able to transform and solve order
     * poly constraints.
     */
    private IDPGPoloSolver (
            final boolean isNat,
            final boolean isTupleNat,
            final GInterpretationMode<BigIntImmutable> form,
            final OPCRange<BigIntImmutable> range,
            final IdpShapeHeuristic idpShapeHeuristic, final StrictMode strictModeParam,
            final IConstraintGenerator contraintGenerator,
            final LogOPCSolverFactory<BigIntImmutable> logOPCSolverFactory) {
        this.isNat = isNat || isTupleNat;
        this.isTupleNat = isTupleNat;
        this.form = form;
        this.range = range;
        this.strictMode = strictModeParam;
        this.contraintGenerator = contraintGenerator;
        this.poloShapeHeuristic = idpShapeHeuristic;
        this.logOPCSolverFactory = logOPCSolverFactory;
    }

    /**
     * Something weird with A-transformation and usable rules.
     * @return False!
     */
    public boolean improvedSolvingSupported() {
        return false;
    }

    /**
     * Try to solve the given problem defined by rule constraints.
     * @param idp The pairs (P).
     * @param rules The rules with the corresponding QActiveCondition.
     * @param active not used.
     * @param allstrict this parameter is not used, use strategy parameter for
     * GPOLONAT!
     * @param aborter The aborter is used to abort calculations after some time.
     * @throws AbortionException Thrown when the aborter gets active.
     * @return A order solving the problem if it can be found.
     */
    @Override
    public IActiveOrder solve(
            final IDPProblem idp,
            final IdpQUsableRules usableRules,
            final boolean active,
            final boolean allstrict,
            final Abortion aborter) throws AbortionException {
                return this.solve(idp, usableRules, aborter);
            }

    /**
     * Try to solve the given problem defined by rule constraints.
     * @param idp The pairs (P).
     * @param aborter The aborter is used to abort calculations after some time.
     * @param rules The rules with the corresponding QActiveCondition.
     * @throws AbortionException Thrown when the aborter gets active.
     * @return A order solving the problem if it can be found.
     */
    @Override
    public IActiveOrder solve(
            final IDPProblem idp,
            final IdpQUsableRules usableRules,
            final Abortion aborter) throws AbortionException {
        // step 1, generate constraints
        final CoeffOrder<BigIntImmutable> coeffOrder = new BigIntImmutableOrder();
        final ConstraintFactory<BigIntImmutable> constraintFactory =
            new SimpleFactory<BigIntImmutable>();
        final GPolyFactory<BigIntImmutable, GPolyVar> coeffFactory =
            new FullSharingFactory<BigIntImmutable, GPolyVar>();

        final List<Citation> citations = new ArrayList<Citation>(1);
        citations.add(Citation.POLO);

        final Ring<BigIntImmutable> ring = new BigIntImmutableRing();
        final CMonoid<GMonomial<GPolyVar>> monoid = new GMonomialMonoid<GPolyVar>();
        final GPolyFactory<BigIntImmutable, GPolyVar> innerPolyFactory = new FullSharingFactory<BigIntImmutable, GPolyVar>();
        final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> outerPolyFactory = new FullSharingFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>();
        final GPolyFlatRing<BigIntImmutable, GPolyVar> flatRing =
            new SimpleGPolyFlatRing<BigIntImmutable, GPolyVar>(ring, monoid);
        final FlatteningVisitor<BigIntImmutable, GPolyVar> fvInner = new FlatteningVisitor<BigIntImmutable, GPolyVar>(flatRing);

        final GPolyFlatRing<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> flatRing2 = new SimpleGPolyFlatRing<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>(innerPolyFactory, monoid);
        final FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> fvOuter = new FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>(flatRing2);

        final LogOPCSolver<BigIntImmutable> opcSolver = this.logOPCSolverFactory.newSolver();
        opcSolver.setFvInner(fvInner);
        opcSolver.setFvOuter(fvOuter);
        opcSolver.setPolyRing(innerPolyFactory);

        // create a new interpretation
        final IDPNonInfInterpretation interpretation =
            IDPNonInfInterpretation.create(
                    this.isNat, this.isTupleNat, idp.getRuleAnalysis(), this.poloShapeHeuristic, outerPolyFactory, coeffFactory, constraintFactory,
                    fvInner, fvOuter, coeffOrder, citations, this.range, this.range.getList().get(0).y, aborter);

        // FreshNameGenerator freshNames = new FreshNameGenerator(idp.getRuleAnalysis().getFunctionSymbols(), FreshNameGenerator.FRIENDLYNAMES);
        interpretation.extend(idp.getRuleAnalysis().getFunctionSymbols(), this.form, aborter);

        final BigIntImmutable one = BigIntImmutable.create(BigInteger.ONE);
        final OPCRange<BigIntImmutable> boolRange =
            new OPCRange<BigIntImmutable>(one, one);

        final Quadruple<OrderPolyConstraint<BigIntImmutable>, IConstraintGeneratorProof, Map<GPolyVar, BigIntImmutable>, Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>>> constraints =
            this.contraintGenerator.generateContraints(idp, usableRules, interpretation, this.strictMode, this.form,
                    boolRange, aborter);

        aborter.checkAbortion();

        // step 2, feed the constraint to the solver and try to solve it

        Logger logger = IDPGPoloSolver.log;
        while (logger.getLevel() == null) {
            logger = IDPGPoloSolver.log.getParent();
        }
        if (logger.getLevel().intValue() >= Level.FINEST.intValue()) {
            final StringBuilder s = new StringBuilder();
            s.append("Problem to solve: \n");
            s.append(idp.export(new PLAIN_Util()));
            s.append("\n");
            s.append(interpretation.export(new PLAIN_Util()));
            s.append("\n");
            s.append(constraints.x.export(new PLAIN_Util()));
            s.append("\n");
            final OPCExportVisitor<BigIntImmutable> exporter = new OPCExportVisitor<BigIntImmutable>(interpretation.getFvInner(), interpretation.getFvOuter(), new PLAIN_Util());
            exporter.applyToWithCleanup(constraints.w);
            s.append("Constraint: \n");
            s.append(exporter);
            s.append("\n");
            IDPGPoloSolver.log.finest(s.toString());
        }

        final Pair<Map<GPolyVar, BigIntImmutable>, Map<OPCLogVar<BigIntImmutable>, Boolean>> solution =
            opcSolver.solveLog(constraints.w, interpretation.getRanges(),
                    interpretation.getNormedCoeffRange(), aborter);


        if (solution == null) {
            innerPolyFactory.clear();
            if (logger.getLevel().intValue() < Level.FINEST.intValue()) {
                final StringBuilder s = new StringBuilder();
                s.append("SOLVING FAILED: \n");
                s.append(constraints.x.export(new PLAIN_Util()));
                s.append("\n");
                s.append(interpretation.export(new PLAIN_Util()));
                s.append("\n");
                final OPCExportVisitor<BigIntImmutable> exporter = new OPCExportVisitor<BigIntImmutable>(interpretation.getFvInner(), interpretation.getFvOuter(), new PLAIN_Util());
                exporter.applyToWithCleanup(constraints.w);
                s.append("Constraint: \n");
                s.append(exporter);
                s.append("\n");
                IDPGPoloSolver.log.fine(s.toString());
            }
            return null;
        }

        aborter.checkAbortion();

        solution.x.putAll(constraints.y);
        // System.err.println("SPECIALIZE!");
        // step 3, build some order out of the solution


        // #############################
        // validation
        // #############################
        final IDPGInterpretation specializedInter =
            interpretation.specialize(solution.x, solution.y, ring.zero(), aborter);

        // cleanup values found by sat solver, we will recompute and optimize them
        for (final GeneralizedRule dp : idp.getP()) {
            specializedInter.resetBoolConstantValue(ConstantType.StrictOrientation, dp);
            specializedInter.resetBoolConstantValue(ConstantType.CompareToNonInfConstant, dp);
        }

        final Quadruple<OrderPolyConstraint<BigIntImmutable>, Map<GeneralizedRule, OrderPolyConstraint<BigIntImmutable>>, IConstraintGeneratorProof, Map<GPolyVar, BigIntImmutable>> validation =
            this.contraintGenerator.validate(idp, usableRules, specializedInter, constraints.z, aborter);

        // validate side constraints
        LogOPCSolver<BigIntImmutable> validationOpcSolver = opcSolver;
        // sat 4J
        final NatOPCSatSolver.Arguments sat4JArgs = new NatOPCSatSolver.Arguments();
        sat4JArgs.engine = new SAT4JEngine(new SAT4JEngine.Arguments());
        validationOpcSolver = new NatOPCSatSolver(sat4JArgs);

        boolean solutionValid = true;
        Map<GPolyVar, BigIntImmutable> validatingSolution =
            opcSolver.solve(validation.w, specializedInter.getRanges(),
                    interpretation.getNormedCoeffRange(), aborter);
        solutionValid &= validatingSolution != null;
        if (!solutionValid && Globals.useAssertions && Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
            System.err.println("Error validating side constraints");
        }

        // validate dp constraints optimizing the solution
        if (solutionValid) {
            final OrderPolyFactory<BigIntImmutable> orderFact = interpretation.getFactory();
            final OrderPoly<BigIntImmutable> onePoly = orderFact.wrap(outerPolyFactory.buildFromCoeff(innerPolyFactory.buildFromCoeff(BigIntImmutable.ONE)));
            for (final Map.Entry<GeneralizedRule, OrderPolyConstraint<BigIntImmutable>> dpConstraint : validation.x.entrySet()) {
                boolean validatedNormal = false;

                BigIntImmutable value = specializedInter.getBoolConstantValue(ConstantType.StrictOrientation, dpConstraint.getKey());
                if (value == null || value.equals(BigIntImmutable.ZERO)) {
                    final OrderPolyConstraint<BigIntImmutable> enhancedConstr = constraintFactory.createAnd(dpConstraint.getValue(),
                            constraintFactory.createWithQuantifier(orderFact.buildFromCoeff(interpretation.getBoolConstantVar(ConstantType.StrictOrientation, dpConstraint.getKey())), onePoly, ConstraintType.EQ));
                    validatingSolution =
                        validationOpcSolver.solve(enhancedConstr, specializedInter.getRanges(),
                                interpretation.getNormedCoeffRange(), aborter);
                    if (validatingSolution != null) {
                        validatedNormal = true;
                        specializedInter.setBoolConstantValue(ConstantType.StrictOrientation, dpConstraint.getKey(), BigIntImmutable.ONE);
                    }
                }

                if (!specializedInter.isTupleNat()) {
                    value =
                        specializedInter.getBoolConstantValue(
                            ConstantType.CompareToNonInfConstant,
                            dpConstraint.getKey());
                    if (value == null || value.equals(BigIntImmutable.ZERO)) {
                        final OrderPolyConstraint<BigIntImmutable> enhancedConstr =
                            constraintFactory.createAnd(
                                dpConstraint.getValue(),
                                constraintFactory.createWithQuantifier(
                                    orderFact.buildFromCoeff(interpretation.getBoolConstantVar(
                                        ConstantType.CompareToNonInfConstant,
                                        dpConstraint.getKey())), onePoly,
                                    ConstraintType.EQ));
                        validatingSolution =
                            validationOpcSolver.solve(enhancedConstr,
                                specializedInter.getRanges(),
                                interpretation.getNormedCoeffRange(), aborter);
                        if (validatingSolution != null) {
                            validatedNormal = true;
                            specializedInter.setBoolConstantValue(
                                ConstantType.CompareToNonInfConstant,
                                dpConstraint.getKey(), BigIntImmutable.ONE);
                        }
                    }
                } else {
                    specializedInter.setBoolConstantValue(
                        ConstantType.CompareToNonInfConstant,
                        dpConstraint.getKey(), BigIntImmutable.ONE);
                }

                if (!validatedNormal) {
                    validatingSolution =
                        validationOpcSolver.solve(dpConstraint.getValue(), specializedInter.getRanges(),
                                interpretation.getNormedCoeffRange(), aborter);
                    if (validatingSolution == null) {
                        solutionValid = false;
                        if (Globals.useAssertions && Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                            System.err.println("Error validating DP: " + dpConstraint.getKey());
                        }
                        break;
                    }
                }
            }
        }
        innerPolyFactory.clear();
        if (!solutionValid) {
            if (Globals.useAssertions && Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                final StringBuilder s = new StringBuilder();
                s.append("VALIDATION FAILED:\n");
                s.append("Ranges"+"\n");

                s.append(interpretation.export(new PLAIN_Util())+"\n");
                s.append(constraints.x.export(new PLAIN_Util())+"\n");
                s.append(interpretation.getRanges()+"\n");
                s.append("Solution"+"\n");
                s.append(solution+"\n");
                s.append(specializedInter.export(new PLAIN_Util())+"\n");
                s.append(validation.y.export(new PLAIN_Util()));
                System.err.println(s.toString());
                assert(false);
            }
            return null;
        }

        // System.err.println("INTERPRETATION : \n" + interpretation.export(new PLAIN_Util()));
        // System.err.println("SOLVING PROOF: \n" + constraints.x.export(new PLAIN_Util()));

        /*
        System.err.println("ACTIVE CONDITIONS: ");
        for (Map.Entry<GeneralizedRule, IActiveCondition> entry : usableRules.getActive().entrySet()) {
            System.err.println("CONDITION: " + entry.getKey() + "\n" + entry.getValue());
        }*/
        // System.err.println("SOLUTION: " + solution);

        final GPOLONonInf solvingOrder =
            new GPOLONonInf(specializedInter, validation.y);
        return solvingOrder;
    }

    @Override
    public String toString() {
        final StringBuilder b = new StringBuilder();
        b.append("IDPGPoloSolver:\n");
        b.append("Range: ");
        b.append(this.range);
        b.append("\nIsNat: ");
        b.append(this.isNat);
        b.append("\nInterpretation Shape Heuristic: ");
        b.append(this.poloShapeHeuristic);
        b.append("\nConstraint Generator: ");
        b.append(this.contraintGenerator);
        return b.toString();
    }

    /**
     * @return the isNat
     */
    public boolean getIsNat() {
        return this.isNat;
    }

    public static class Arguments {
        public IdpShapeHeuristic poloShapeHeuristic = new IdpCand1ShapeHeuristic(new IdpCand1ShapeHeuristic.Arguments());
        public boolean nat = false;
        public boolean natTuple = false;
        public int degree = -1;
        public int maxSimpleDegree = 1;
        public OPCRange<BigIntImmutable> range = new OPCRange<BigIntImmutable>(BigIntImmutable.MINUS_ONE, BigIntImmutable.TWO);
        public StrictMode strictMode = StrictMode.AUTOSTRICT;
        public IConstraintGenerator constraintGenerator;
        public LogOPCSolverFactory<BigIntImmutable> opcSolver;
    }
}

