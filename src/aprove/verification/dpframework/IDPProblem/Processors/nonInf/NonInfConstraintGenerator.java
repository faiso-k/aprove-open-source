/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.nonInf;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.DPConstraints.Implication;
import aprove.verification.dpframework.DPConstraints.Predicate.*;
import aprove.verification.dpframework.DPConstraints.idp.*;
import aprove.verification.dpframework.DPConstraints.idp.IdpInductionCalculus.*;
import aprove.verification.dpframework.DPProblem.SMT_LIA.*;
import aprove.verification.dpframework.DPProblem.SMT_LIA.SMTLIB.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.CondGPCToGPCTransformer.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.IDPGInterpretation.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class NonInfConstraintGenerator implements IConstraintGenerator {

    protected static final BigInteger TWO = BigInteger.valueOf(2);

    // private static final String BOOL_USESWITCH_PREFIX = "useBool_";

    /**
     * Number of Inductions per Equality.
     */
    private final int inductionCounter;
    private final int rewritingCounter;

    private final ISMTChecker smtEngine;

    private final IPathGenerator pathGenerator;

    private final SearchMode uncondMode;
    private final int dropOrientConditions;

    @ParamsViaArgumentObject
    public NonInfConstraintGenerator(final Arguments arguments) {
        this.inductionCounter = arguments.inductionCounter;
        this.smtEngine = arguments.smtEngine;
        this.pathGenerator = arguments.pathGenerator;
        this.rewritingCounter = arguments.rewritingCounter;
        this.uncondMode = arguments.uncondMode;
        this.dropOrientConditions = arguments.dropOrientConditions;
    }

    @Override
    public Quadruple<OrderPolyConstraint<BigIntImmutable>, IConstraintGeneratorProof, Map<GPolyVar, BigIntImmutable>, Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>>> generateContraints(final IDPProblem idp,
        final IdpQUsableRules usableRules,
        final IDPGInterpretation gInter,
        final StrictMode strictMode,
        final GInterpretationMode<BigIntImmutable> form,
        final OPCRange<BigIntImmutable> boolRange,
        final Abortion aborter) throws AbortionException {
        final IDPNonInfInterpretation interpretation = (IDPNonInfInterpretation) gInter;
        final IDPOptions options = new IDPOptions(this.pathGenerator, this.inductionCounter, this.rewritingCounter);

        final InductionCalculusProof icProof = new InductionCalculusProof(idp, options);
        final IdpNonInfIC indCalculus =
            new IdpNonInfIC(idp, icProof, options, interpretation, IdpNonInfIC.FULL_STRATEGY, aborter);
        final Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> termConstraints =
            indCalculus.createConstraintSetProRule();

        int chainCount = 0;
        int stepCount = 0;
        final Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> savedConstraintSetProRule =
            new LinkedHashMap<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>>();
        for (final Map.Entry<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> entry : termConstraints.entrySet()) {
            final Map<List<GeneralizedRule>, List<Implication>> newInnerMap =
                new LinkedHashMap<List<GeneralizedRule>, List<Implication>>();
            chainCount += entry.getValue().size();
            for (final Map.Entry<List<GeneralizedRule>, List<Implication>> innerEntry : entry.getValue().entrySet()) {
                stepCount += innerEntry.getValue().size();
                newInnerMap.put(new ArrayList<GeneralizedRule>(innerEntry.getKey()), new ArrayList<Implication>(
                    innerEntry.getValue()));
            }
            savedConstraintSetProRule.put(entry.getKey(), newInnerMap);
        }
        // System.err.println("CHAINCOUNT: " + chainCount + " with " + stepCount + " steps");

        /*
        System.out.println("TERM MAP: ");
        indCalculus.showMap(termConstraints);
        System.out.println("MAP END");
         */
        final Quadruple<OrderPolyConstraint<BigIntImmutable>, Map<GeneralizedRule, OrderPolyConstraint<BigIntImmutable>>, IConstraintGeneratorProof, Map<GPolyVar, BigIntImmutable>> res =
            this.generateContraints(idp, usableRules, interpretation, indCalculus, icProof, termConstraints, aborter);
        OrderPolyConstraint<BigIntImmutable> constr = res.w;
        final ConstraintFactory<BigIntImmutable> fact = interpretation.getConstraintFactory();
        for (final OrderPolyConstraint<BigIntImmutable> dpConstr : res.x.values()) {
            constr = fact.createAnd(constr, dpConstr);
        }
        return new Quadruple<OrderPolyConstraint<BigIntImmutable>, IConstraintGeneratorProof, Map<GPolyVar, BigIntImmutable>, Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>>>(
            constr, res.y, res.z, savedConstraintSetProRule);
    }

    @Override
    public Quadruple<OrderPolyConstraint<BigIntImmutable>, Map<GeneralizedRule, OrderPolyConstraint<BigIntImmutable>>, IConstraintGeneratorProof, Map<GPolyVar, BigIntImmutable>> validate(final IDPProblem idp,
        final IdpQUsableRules usableRules,
        final IDPGInterpretation gInter,
        final Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> savedConstraintSetProRule,
        final Abortion aborter) throws AbortionException {
        final IDPNonInfInterpretation interpretation = (IDPNonInfInterpretation) gInter;
        final IDPOptions options = new IDPOptions(this.pathGenerator, this.inductionCounter, this.rewritingCounter);

        final InductionCalculusProof icProof = new InductionCalculusProof(idp, options);
        final IdpNonInfIC indCalculus =
            new IdpNonInfIC(idp, icProof, options, interpretation, IdpNonInfIC.VALIDATE_FULL_STRATEGY, aborter);

        /*
        System.out.println("VALIDATE MAP: ");
        indCalculus.showMap(savedConstraintSetProRule);
        System.out.println("MAP END");
        */
        return this.generateContraints(idp, usableRules, interpretation, indCalculus, icProof, savedConstraintSetProRule,
            aborter);
    }

    /**
     *
     * @param idp
     * @param usableRules
     * @param interpretation
     * @param indCalculus
     * @param icProof
     * @param termConstraints
     * @param aborter
     * @return w: usable rules and side constrains, x: constraints for each DP, y: the proof, z: predefined variables (optimization)
     * @throws AbortionException
     */
    public Quadruple<OrderPolyConstraint<BigIntImmutable>, Map<GeneralizedRule, OrderPolyConstraint<BigIntImmutable>>, IConstraintGeneratorProof, Map<GPolyVar, BigIntImmutable>> generateContraints(final IDPProblem idp,
        final IdpQUsableRules usableRules,
        final IDPNonInfInterpretation interpretation,
        final IdpNonInfIC indCalculus,
        final InductionCalculusProof icProof,
        final Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> termConstraints,
        final Abortion aborter) throws AbortionException {
        // inject constraints

        indCalculus.simplify(termConstraints);
        aborter.checkAbortion(); // indCalculus.simplify() might take ages

        // System.out.println("###################### SIMPLIFIED ##########################");
        final CondGPCToGPCTransformer<BigIntImmutable> transformer =
            new CondGPCToGPCTransformer<BigIntImmutable>(interpretation.getFactory(),
                interpretation.getConstraintFactory());

        final ConstraintFactory<BigIntImmutable> constraintFactory = interpretation.getConstraintFactory();
        final OrderPolyFactory<BigIntImmutable> orderFactory = interpretation.getFactory();
        final Map<GPolyVar, OPCRange<BigIntImmutable>> ranges = interpretation.getRanges();
        // constraints.add(lateUsableRules);

        final Pair<Semiring<BigIntImmutable>, CMonoid<GMonomial<GPolyVar>>> innerRingMonoid =
            interpretation.getInnerRingMonoid();

        final Map<GeneralizedRule, OrderPolyConstraint<BigIntImmutable>> dpConstraints =
            new LinkedHashMap<GeneralizedRule, OrderPolyConstraint<BigIntImmutable>>();

        for (final Map.Entry<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> nodePaths : termConstraints.entrySet()) {
            final Set<OrderPolyConstraint<BigIntImmutable>> constr =
                new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
            for (final List<Implication> implications : nodePaths.getValue().values()) {
                this.processImplications(implications, constr, interpretation, transformer, constraintFactory, orderFactory,
                    innerRingMonoid, aborter, ranges);
            }
            dpConstraints.put(nodePaths.getKey(), constraintFactory.createAnd(constr));
            aborter.checkAbortion();
        }

        final Set<OrderPolyConstraint<BigIntImmutable>> sideConstraints =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        // process usable rules
        final List<Implication> urConstraints = new ArrayList<Implication>(idp.getR().size() * 2);
        sideConstraints.add(this.addUsableRulesConstraints(urConstraints, idp, interpretation, aborter));
        final Map<List<GeneralizedRule>, List<Implication>> urPathMap =
            new LinkedHashMap<List<GeneralizedRule>, List<Implication>>();
        urPathMap.put(null, urConstraints);
        final Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> usableConstraints =
            new LinkedHashMap<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>>();
        usableConstraints.put(null, urPathMap);
        indCalculus.simplify(usableConstraints);
        this.addStrictConstraints(sideConstraints, idp, interpretation);
        this.processImplications(urConstraints, sideConstraints, interpretation, transformer, constraintFactory,
            orderFactory, innerRingMonoid, aborter, ranges);
        // Strict
        aborter.checkAbortion(); // indCalculus.simplify() might take ages
        sideConstraints.add(interpretation.getUsableRulesConstraints());

        final OrderPolyConstraint<BigIntImmutable> sideConstraint = constraintFactory.createAnd(sideConstraints);
        final Map<GPolyVar, BigIntImmutable> values = new LinkedHashMap<GPolyVar, BigIntImmutable>();
        return new Quadruple<OrderPolyConstraint<BigIntImmutable>, Map<GeneralizedRule, OrderPolyConstraint<BigIntImmutable>>, IConstraintGeneratorProof, Map<GPolyVar, BigIntImmutable>>(
            sideConstraint, dpConstraints, new NonInfConstraintGeneratorProof(icProof, null), values);
    }

    protected void processImplications(final List<Implication> implications,
        final Set<OrderPolyConstraint<BigIntImmutable>> constraints,
        final IDPNonInfInterpretation interpretation,
        final CondGPCToGPCTransformer<BigIntImmutable> transformer,
        final ConstraintFactory<BigIntImmutable> constraintFactory,
        final OrderPolyFactory<BigIntImmutable> orderFactory,
        final Pair<Semiring<BigIntImmutable>, CMonoid<GMonomial<GPolyVar>>> innerRingMonoid,
        final Abortion aborter,
        final Map<GPolyVar, OPCRange<BigIntImmutable>> ranges) {
        final Map<OrderPolyConstraint<BigIntImmutable>, Set<OrderPolyConstraint<BigIntImmutable>>> usableRuleConstraints =
            new LinkedHashMap<OrderPolyConstraint<BigIntImmutable>, Set<OrderPolyConstraint<BigIntImmutable>>>();
        final GPolyFactory<BigIntImmutable, GPolyVar> innerFactory = interpretation.getFactory().getInnerFactory();
        final GPoly<BigIntImmutable, GPolyVar> coeffZero = innerFactory.zero();
        for (final Implication implication : implications) {
            // System.out.println("implication " );
            final Map<OrderPoly<BigIntImmutable>, Integer> conds =
                new LinkedHashMap<OrderPoly<BigIntImmutable>, Integer>();
            final Iterator<Constraint> i = implication.getConditions().iterator();
            while (i.hasNext()) {
                final Constraint c = i.next();
                if (c.isPolyAtom()) {
                    final PolyAtom<BigIntImmutable> cond = (PolyAtom<BigIntImmutable>) c;
                    if (cond.getRecommendation() < 0) {
                        continue;
                    }
                    if (cond.getRelation() == ConstraintType.GE && !this.canBeNegative(interpretation, cond.getLhs())) {
                        //System.err.println("Removed condition " + polyString(interpretation, cond.getLhs()));
                        continue;
                    }
                    // remove gt for condition
                    if (cond.getRelation() == ConstraintType.GT) {
                        conds.put(
                            orderFactory.wrap(orderFactory.getFactory().minus(cond.getLhs(),
                                orderFactory.getFactory().one())), cond.getRecommendation());
                        // System.out.println("cond; " + polyString(interpretation, orderFactory.getFactory().minus(cond.getLhs(), orderFactory.getFactory().one())));
                    } else if (cond.getRelation() == ConstraintType.EQ) {
                        conds.put(orderFactory.wrap(cond.getLhs()), cond.getRecommendation());
                        conds.put(orderFactory.wrap(orderFactory.getFactory().getInverse(cond.getLhs())),
                            cond.getRecommendation());
                    } else {
                        conds.put(orderFactory.wrap(cond.getLhs()), cond.getRecommendation());
                        // System.out.println("cond; " + polyString(interpretation, cond.getLhs()));
                    }
                    // System.out.println("cond; " + polyString(interpretation, normalized));
                    // System.err.println("Poly Constraint: " + cond.getULeft() + " / " + cond.getLeft() + " -> " + cond.getURight() +  " / " + cond.getRight());
                } else if (c.isUsableAtom()) {
                    final UsableAtom<BigIntImmutable> usable = (UsableAtom<BigIntImmutable>) c;

                    constraints.add(this.getTermUsableOriented(usable.getT(), usable.getOrientation(), interpretation));
                }
            }

            // check if conds are solvable, otherwise ignore implication
            /*
            if (!isSolvable(conds, interpretation, aborter)) {
                // System.err.println("SMT removed trivially satisfied implication");
                continue;
            }*/

            List<Constraint> conclusions;
            if (implication.getConclusion().isConstraintSet()) {
                conclusions = new ArrayList<Constraint>((ConstraintSet) implication.getConclusion());
            } else {
                conclusions = new ArrayList<Constraint>();
                conclusions.add(implication.getConclusion());
            }
            int size = conclusions.size();
            for (int j = 0; j < size; j++) {
                final Constraint c = conclusions.get(j);
                if (c.isPolyAtom()) {
                    final PolyAtom<BigIntImmutable> conclusion = (PolyAtom<BigIntImmutable>) c;
                    GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> conclusionPoly;
                    // remove gt for conclusion
                    if (conclusion.getRelation() == ConstraintType.GT) {
                        conclusionPoly =
                            orderFactory.getFactory().minus(conclusion.getLhs(), orderFactory.getFactory().one());
                    } else if (conclusion.getRelation() == ConstraintType.EQ) {
                        conclusions.add(PolyAtom.create(
                            interpretation.getFactory().getFactory().getInverse(conclusion.getLhs()),
                            ConstraintType.GE, interpretation, conclusion.getTermAtom(), conclusion.getLeft(),
                            conclusion.getRight(), conclusion.getRecommendation()));
                        size++;
                        conclusionPoly = conclusion.getLhs();
                    } else {
                        conclusionPoly = conclusion.getLhs();
                    }

                    // System.out.println("conclusionPoly; " + polyString(interpretation, conclusionPoly));

                    boolean isBound = false;
                    // OrderPolyConstraint<BigIntImmutable> boundSwitch = null;
                    if (conclusion.getTermAtom() != null && conclusion.getTermAtom().isPredicate()) {
                        final Predicate pred = (Predicate) conclusion.getTermAtom();
                        if (pred.getKind() == Kind.NonInfConstantCompare) {
                            isBound = true;
                            // boundSwitch = interpretation.getLogVarConstant(ConstantType.CompareToNonInfConstant, pred.getOrigRule());
                        }
                    }
                    GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> uncondPoly;
                    final Set<Pair<GPoly<BigIntImmutable, GPolyVar>, ConstraintType>> sortOtimizationConstraints =
                        new LinkedHashSet<Pair<GPoly<BigIntImmutable, GPolyVar>, ConstraintType>>();
                    if (conds.size() > 0) {
                        Set<OrderPoly<BigIntImmutable>> filteredConds;
                        if (isBound || this.dropOrientConditions <= 0) {
                            filteredConds = conds.keySet();
                        } else {
                            filteredConds = new LinkedHashSet<OrderPoly<BigIntImmutable>>();
                            for (final Map.Entry<OrderPoly<BigIntImmutable>, Integer> entry : conds.entrySet()) {
                                if (entry.getValue() >= this.dropOrientConditions) {
                                    filteredConds.add(entry.getKey());
                                }
                            }
                        }
                        uncondPoly =
                            transformer.transform(this.uncondMode, filteredConds, conclusionPoly, ranges,
                                sortOtimizationConstraints);
                    } else {
                        uncondPoly = conclusionPoly;
                    }

                    if (!uncondPoly.isFlat(interpretation.getPolyRing(), interpretation.getMonoid())) {
                        uncondPoly = interpretation.getFvOuter().applyTo(uncondPoly);
                    }
                    // System.err.println("uncondPoly: " + polyString(interpretation, uncondPoly));

                    // find variables that can be set to zero
                    final Map<GPolyVar, GPoly<BigIntImmutable, GPolyVar>> zeroVars =
                        new LinkedHashMap<GPolyVar, GPoly<BigIntImmutable, GPolyVar>>();
                    final VarSubstitutionVisitor<BigIntImmutable, GPolyVar> zeroVarsVisitor =
                        new VarSubstitutionVisitor<BigIntImmutable, GPolyVar>(zeroVars, innerFactory, null);
                    for (final Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> entry : uncondPoly.getMonomials(
                        interpretation.getPolyRing(), interpretation.getMonoid()).entrySet()) {
                        final Triple<GPoly<BigIntImmutable, GPolyVar>, GPoly<BigIntImmutable, GPolyVar>, Set<GPoly<BigIntImmutable, GPolyVar>>> sortedPoly =
                            NonInfConstraintGenerator.sort(interpretation, entry.getValue());
                        sortedPoly.x = interpretation.getFvInner().applyTo(sortedPoly.x);
                        sortedPoly.y = interpretation.getFvInner().applyTo(sortedPoly.y);
                        if (sortedPoly.x.isConstant()
                            && sortedPoly.x.getConstantPart(innerRingMonoid).getBigInt().signum() == 0
                            && sortedPoly.z.isEmpty()) {
                            for (final GPolyVar var : sortedPoly.y.getVariables()) {
                                final String varName = var.getName();
                                if (varName.startsWith(CondGPCToGPCTransformer.P_COEFF_PREFIX)
                                    || varName.startsWith(CondGPCToGPCTransformer.Q_COEFF_PREFIX)) {
                                    zeroVars.put(var, coeffZero);
                                }
                            }
                        }
                    }

                    final Set<GPolyVar> usedVars = new LinkedHashSet<GPolyVar>();
                    for (final Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> entry : uncondPoly.getMonomials(
                        interpretation.getPolyRing(), interpretation.getMonoid()).entrySet()) {

                        final Triple<GPoly<BigIntImmutable, GPolyVar>, GPoly<BigIntImmutable, GPolyVar>, Set<GPoly<BigIntImmutable, GPolyVar>>> sortedPoly =
                            NonInfConstraintGenerator.sort(interpretation, zeroVarsVisitor.applyTo(entry.getValue()));
                        sortedPoly.x = interpretation.getFvInner().applyTo(sortedPoly.x);
                        sortedPoly.y = interpretation.getFvInner().applyTo(sortedPoly.y);
                        // remove constants
                        if (sortedPoly.y.isConstant()
                            && sortedPoly.y.getConstantPart(innerRingMonoid).getBigInt().signum() == 0) {
                            if (!this.canBeInnerNegative(interpretation, sortedPoly.x)) {
                                // System.err.println("***** Removed " +innerPolyString(interpretation, sortedPoly.x) + " >= " + innerPolyString(interpretation, sortedPoly.y));
                                continue;
                            }
                        }
                        usedVars.addAll(sortedPoly.x.getVariables());
                        usedVars.addAll(sortedPoly.y.getVariables());
                        /*
                         * NOT SOUND!
                        if (sortedPoly.x.isConstant() && sortedPoly.x.getConstantPart(innerRingMonoid).getBigInt().signum() == 0
                                && sortedPoly.y.getConstantPart(innerRingMonoid).getBigInt().signum() == 0) {
                            Set<GPolyVar> vars = sortedPoly.y.getVariables();
                            if (vars.size() == 1) {
                                String varName = vars.iterator().next().getName();
                                if (varName.startsWith(CondGPCToGPCTransformer.P_COEFF_PREFIX) || varName.startsWith(CondGPCToGPCTransformer.Q_COEFF_PREFIX)) {
                                    System.err.println("++++ Removed " +innerPolyString(interpretation, sortedPoly.x) + " >= " + innerPolyString(interpretation, sortedPoly.y));
                                    continue;
                                }
                            }
                        }
                         */
                        // search for nonInfC
                        // System.out.println("SORTED: " + innerPolyString(interpretation, sortedPoly.x) + " >= " + innerPolyString(interpretation, sortedPoly.y));
                        // ordinary constraint
                        OrderPolyConstraint<BigIntImmutable> constr = null;
                        /*
                        if (sortedPoly.x.isConstant() && sortedPoly.y.isConstant()) {
                            if (sortedPoly.x.getConstantPart(innerRingMonoid).getBigInt().compareTo(sortedPoly.y.getConstantPart(innerRingMonoid).getBigInt()) < 0) {
                                // System.err.println("***** Unsolvable " + polyString(interpretation, conclusionPoly));
                                // System.err.println("***** " + implication);
                                constr = constraintFactory.createFalse();
                                // trivially unsolvable
                            }
                        }*/
                        if (constr == null) { // false otherwise
                            constr =
                                constraintFactory.createWithQuantifier(
                                    interpretation.getFactory().wrap(orderFactory.buildFromCoeff(sortedPoly.x)),
                                    interpretation.getFactory().wrap(orderFactory.buildFromCoeff(sortedPoly.y)),
                                    ConstraintType.GE);
                            //arbitrary constants filtering
                            if (sortedPoly.z.size() > 0) {
                                for (final GPoly<BigIntImmutable, GPolyVar> p : sortedPoly.z) {
                                    final Pair<GPoly<BigIntImmutable, GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> sorted =
                                        SortNatPoly.sort(interpretation, p);
                                    constr =
                                        constraintFactory.createAnd(
                                            constraintFactory.createWithQuantifier(
                                                orderFactory.buildFromCoeff(sorted.x),
                                                orderFactory.buildFromCoeff(sorted.y), ConstraintType.EQ), constr);
                                }
                            }
                        }
                        OrderPolyConstraint<BigIntImmutable> constraint;
                        // nonInfSolution
                        final OrderPolyConstraint<BigIntImmutable> nonInfCSolution =
                            this.solvedByNonInfC(interpretation, entry.getValue());
                        if (nonInfCSolution != null) {
                            // System.err.println("***** NonInfC Solution" +innerPolyString(interpretation, sortedPoly.x) + " >= " + innerPolyString(interpretation, sortedPoly.y));
                            // System.err.println(nonInfCSolution);
                            constraint = constraintFactory.createOr(constr, nonInfCSolution);
                        } else {
                            constraint = constr;
                        }

                        /*
                        if (isBound) {
                            constraint = constraintFactory.createOr(constraintFactory.createNot(boundSwitch), constraint);
                        }*/

                        // active constraints
                        if (implication.getData() != null && implication.getData() instanceof OrderPolyConstraint) {
                            final OrderPolyConstraint<BigIntImmutable> inactive =
                                (OrderPolyConstraint<BigIntImmutable>) implication.getData();
                            Set<OrderPolyConstraint<BigIntImmutable>> usableCs = usableRuleConstraints.get(inactive);
                            if (usableCs == null) {
                                usableCs = new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>(1);
                                usableRuleConstraints.put(inactive, usableCs);
                            }
                            usableCs.add(constraint);
                        } else {
                            // System.err.println("Constraint: " + constraint);
                            constraints.add(constraint);
                        }
                    }
                    for (final Pair<GPoly<BigIntImmutable, GPolyVar>, ConstraintType> sortC : sortOtimizationConstraints) {
                        if (usedVars.containsAll(sortC.x.getVariables())) {
                            final Pair<GPoly<BigIntImmutable, GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> sorted =
                                SortNatPoly.sort(interpretation, sortC.x);
                            constraints.add(constraintFactory.createWithQuantifier(
                                orderFactory.buildFromCoeff(sorted.x), orderFactory.buildFromCoeff(sorted.y), sortC.y));
                        }
                    }

                } else if (c.isUsableAtom()) {
                    final UsableAtom<BigIntImmutable> usable = (UsableAtom<BigIntImmutable>) c;
                    constraints.add(this.getTermUsableOriented(usable.getT(), usable.getOrientation(), interpretation));
                } else {
                    throw new UnsupportedOperationException("Unknon conclusion type: " + c);
                }
            }
        }
        for (final Map.Entry<OrderPolyConstraint<BigIntImmutable>, Set<OrderPolyConstraint<BigIntImmutable>>> usableEntry : usableRuleConstraints.entrySet()) {
            constraints.add(constraintFactory.createOr(usableEntry.getKey(),
                constraintFactory.createAnd(usableEntry.getValue())));
        }
    }

    /**
     * @param sortedPoly.z must be flattened!
     * @return null if can not be solved, new constraint if nonInfC solves
     */
    private OrderPolyConstraint<BigIntImmutable> solvedByNonInfC(final IDPNonInfInterpretation interpretation,
        final GPoly<BigIntImmutable, GPolyVar> uncondPoly) {
        final GPolyFactory<BigIntImmutable, GPolyVar> innerFac = interpretation.getFactory().getInnerFactory();
        GPoly<BigIntImmutable, GPolyVar> sum = null;
        if (!uncondPoly.isFlat(interpretation.getInnerRingMonoid())) {
            interpretation.getFvInner().applyTo(uncondPoly);
        }
        for (final Map.Entry<GMonomial<GPolyVar>, BigIntImmutable> entry : uncondPoly.getMonomials(
            interpretation.getInnerRingMonoid()).entrySet()) {
            if (entry.getKey().getExponents().containsKey(interpretation.getNonInfBound())
                && entry.getKey().getExponents().get(interpretation.getNonInfBound()).mod(NonInfConstraintGenerator.TWO).signum() > 0) {
                final Collection<GPolyVar> vars = new ArrayList<GPolyVar>();
                for (final Map.Entry<GPolyVar, BigInteger> varEntry : entry.getKey().getExponents().entrySet()) {
                    if (varEntry.getKey().equals(interpretation.getNonInfBound())) {
                        continue;
                    }
                    for (int i = varEntry.getValue().intValue() - 1; i >= 0; i--) {
                        vars.add(varEntry.getKey());
                    }
                }
                if (sum == null) {
                    sum = innerFac.getInverse(innerFac.concat(entry.getValue(), innerFac.buildVariables(vars)));
                } else {
                    sum = innerFac.minus(sum, innerFac.concat(entry.getValue(), innerFac.buildVariables(vars)));
                }
            }
        }
        if (sum != null) {
            final Pair<GPoly<BigIntImmutable, GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> sorted =
                SortNatPoly.sort(interpretation, sum);
            return interpretation.getConstraintFactory().createWithQuantifier(
                interpretation.getFactory().buildFromCoeff(sorted.x),
                interpretation.getFactory().buildFromCoeff(sorted.y), ConstraintType.GT);
        } else {
            return null;
        }
    }

    private boolean canBeNegative(final IDPNonInfInterpretation interpretation,
        GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> poly) {
        if (!poly.isFlat(interpretation.getPolyRing(), interpretation.getMonoid())) {
            poly = interpretation.getFvOuter().applyTo(poly);
        }
        for (final Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> entry : poly.getMonomials(
            interpretation.getPolyRing(), interpretation.getMonoid()).entrySet()) {
            if (this.canBeInnerNegative(interpretation, entry.getValue())) {
                return true;
            }
            for (final Map.Entry<GPolyVar, BigInteger> varEntry : entry.getKey().getExponents().entrySet()) {
                if (varEntry.getValue().mod(NonInfConstraintGenerator.TWO).signum() != 0) {
                    return true;
                }
            }
        }
        return false;
    }

    private boolean canBeInnerNegative(final IDPNonInfInterpretation interpretation,
        GPoly<BigIntImmutable, GPolyVar> coeff) {
        if (!coeff.isFlat(interpretation.getRing(), interpretation.getMonoid())) {
            coeff = interpretation.getFvInner().applyTo(coeff);
        }
        for (final Map.Entry<GMonomial<GPolyVar>, BigIntImmutable> coeffEntry : coeff.getMonomials(
            interpretation.getRing(), interpretation.getMonoid()).entrySet()) {
            if (coeffEntry.getValue().getBigInt().signum() < 0) {
                return true;
            }
        }
        return false;
    }

    protected void addStrictConstraints(final Collection<OrderPolyConstraint<BigIntImmutable>> constraints,
        final IDPProblem idp,
        final IDPNonInfInterpretation polyInterpretation) {
        // TODO: use strictMode

        final OrderPolyFactory<BigIntImmutable> factory = polyInterpretation.getFactory();
        constraints.add(polyInterpretation.getConstraintFactory().createWithQuantifier(
            factory.buildFromCoeff(factory.getInnerFactory().plus(
                polyInterpretation.getBoolConstants(ConstantType.StrictOrientation))), ConstraintType.GT));
        final Set<GPoly<BigIntImmutable, GPolyVar>> unknownNonInfConst =
            polyInterpretation.getBoolUnknownConstants(ConstantType.CompareToNonInfConstant);
        if (!unknownNonInfConst.isEmpty()) {
            constraints.add(polyInterpretation.getConstraintFactory().createWithQuantifier(
                factory.buildFromCoeff(factory.getInnerFactory().plus(unknownNonInfConst)), ConstraintType.GT));
        }
        /*
        Set<OrderPolyConstraint<BigIntImmutable>> nonInfLogVars = polyInterpretation.getRuleLogVars(ConstantType.CompareToNonInfConstant);
        if (nonInfLogVars.size() > 0) {
            constraints.add(polyInterpretation.getConstraintFactory().createOr(nonInfLogVars));
        }*/
        // System.out.println("Strict Total: " + polyString(polyInterpretation, factory.getFactory().buildFromCoeff(factory.getInnerFactory().plus(polyInterpretation.getBoolConstants(ConstantType.StrictOrientation)))));

    }

    /**
     * Builds conjunction for encoded usable rules
     * @param t
     * @param k
     * @param consideredUsableRules
     * @param consideredUsableTerms
     * @return
     */
    protected OrderPolyConstraint<BigIntImmutable> getTermUsableOriented(final TRSTerm t,
        final RelDependency k,
        final IDPNonInfInterpretation interpretation) {
        switch (k) {
        case Increasing:
            return interpretation.getLogVarConstant(ConstantType.UsableInc_1, t);
        case Decreasing:
            return interpretation.getLogVarConstant(ConstantType.UsableDec_m1, t);
        case Independent:
            return interpretation.getConstraintFactory().createTrue();
        default:
            return interpretation.getConstraintFactory().createAnd(
                interpretation.getLogVarConstant(ConstantType.UsableInc_2, t),
                interpretation.getLogVarConstant(ConstantType.UsableDec_2, t));
        }
    }

    protected OrderPolyConstraint<BigIntImmutable> addUsableRulesConstraints(final Collection<Implication> constraints,
        final IDPProblem idp,
        final IDPNonInfInterpretation interpretation,
        final Abortion aborter) throws AbortionException {
        final Pair<Set<Pair<OrderPolyConstraint<BigIntImmutable>, OrderPoly<BigIntImmutable>>>, OrderPolyConstraint<BigIntImmutable>> res =
            interpretation.getUsableRulesConstraintEquations(idp.getRuleAnalysis().getUseableRulesEstimation(null),
                aborter);
        for (final Pair<OrderPolyConstraint<BigIntImmutable>, OrderPoly<BigIntImmutable>> entry : res.x) {
            constraints.add(Implication.create(IdpInductionCalculus.emptyQuantor, IdpInductionCalculus.emptyConditions,
                PolyAtom.create(entry.y, ConstraintType.GE, interpretation, null, null, null, 0), entry.x));
        }
        // System.err.println("OrderPolyConstraint " + res.x + "\n" + res.y);
        return res.y;
    }

    protected boolean isSolvable(final Set<OrderPoly<BigIntImmutable>> conds,
        final IDPNonInfInterpretation interpretation,
        final Abortion aborter) {
        if (conds.isEmpty()) {
            return true;
        }

        final List<ImmutableBoolOp<LIAConstraint>> constraints =
            new ArrayList<ImmutableBoolOp<LIAConstraint>>(conds.size());
        final GPolyFactory<BigIntImmutable, GPolyVar> innerFactory = interpretation.getFactory().getInnerFactory();
        condFor: for (final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> poly : conds) {
            if (!poly.isFlat(interpretation.getPolyRing(), interpretation.getMonoid())) {
                interpretation.getFvOuter().applyTo(poly);
            }
            GPoly<BigIntImmutable, GPolyVar> res = null;
            for (final Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> monomial : poly.getMonomials(
                interpretation.getPolyRing(), interpretation.getMonoid()).entrySet()) {
                final Map<GPolyVar, BigInteger> exponents = monomial.getKey().getExponents();
                // not linear in outer variables?
                if (exponents.size() == 1) {
                    if (exponents.values().iterator().next().compareTo(BigInteger.ONE) == 1) {
                        continue condFor;
                    }
                }
                if (exponents.size() > 1) {
                    continue condFor;
                }
                GPoly<BigIntImmutable, GPolyVar> coeff = monomial.getValue();
                if (exponents.size() > 0) {
                    if (!coeff.isFlat(interpretation.getRing(), interpretation.getMonoid())) {
                        interpretation.getFvInner().applyTo(coeff);
                    }
                    if (coeff.containsVariable()) {
                        continue condFor;
                    }
                    final BigIntImmutable coeffConstant =
                        coeff.getConstantPart(interpretation.getRing(), interpretation.getMonoid());
                    coeff =
                        innerFactory.concat(coeffConstant,
                            innerFactory.buildVariable(exponents.keySet().iterator().next()));
                }
                if (res == null) {
                    res = coeff;
                } else {
                    res = innerFactory.plus(res, coeff);
                }
            }
            interpretation.getFvInner().applyTo(res);
            if (res != null) {
                constraints.add(ImmutableBoolOp.createAtom(new LIAConstraint(res,
                    interpretation.getFactory().getInnerFactory().zero(), ArithmeticRelation.GE)));
            }
        }
        YNM solution;
        try {
            solution = this.smtEngine.isSatisfiable(ImmutableBoolOp.createConjunction(constraints), aborter);
        } catch (final AbortionException e) {
            solution = YNM.MAYBE;
        }
        return solution != YNM.NO;
    }

    /**
     *
     * @param interpretation
     * @param coeff
     * @return x = left >= right = y; z = parts with arbitrary constants that have to be 0
     */
    public static Triple<GPoly<BigIntImmutable, GPolyVar>, GPoly<BigIntImmutable, GPolyVar>, Set<GPoly<BigIntImmutable, GPolyVar>>> sort(final GInterpretation<BigIntImmutable> interpretation,
        GPoly<BigIntImmutable, GPolyVar> coeff) {
        if (!coeff.isFlat(interpretation.getRing(), interpretation.getMonoid())) {
            coeff = interpretation.getFvInner().applyTo(coeff);
        }
        final Set<GPoly<BigIntImmutable, GPolyVar>> left = new LinkedHashSet<GPoly<BigIntImmutable, GPolyVar>>();
        final Set<GPoly<BigIntImmutable, GPolyVar>> right = new LinkedHashSet<GPoly<BigIntImmutable, GPolyVar>>();
        final Set<GPoly<BigIntImmutable, GPolyVar>> arbitraryConstantParts =
            new LinkedHashSet<GPoly<BigIntImmutable, GPolyVar>>();
        final GPolyFactory<BigIntImmutable, GPolyVar> factory = interpretation.getFactory().getInnerFactory();
        final Semiring<BigIntImmutable> ring = interpretation.getRing();
        for (final Map.Entry<GMonomial<GPolyVar>, BigIntImmutable> entry : coeff.getMonomials(interpretation.getRing(),
            interpretation.getMonoid()).entrySet()) {
            final Collection<GPolyVar> vars = new ArrayList<GPolyVar>();
            boolean isArbitraryConstant = false;
            for (final Map.Entry<GPolyVar, BigInteger> varEntry : entry.getKey().getExponents().entrySet()) {
                if (varEntry.getKey() instanceof NonInfArbitraryConstant || varEntry.getKey() instanceof NonInfBound) {
                    isArbitraryConstant = true;
                } else {
                    for (int i = varEntry.getValue().intValue() - 1; i >= 0; i--) {
                        vars.add(varEntry.getKey());
                    }
                }
            }
            if (isArbitraryConstant) {
                arbitraryConstantParts.add(factory.concat(entry.getValue(), factory.buildVariables(vars)));
            } else {
                if (entry.getValue().getBigInt().signum() >= 0) {
                    left.add(factory.concat(entry.getValue(), factory.buildVariables(vars)));
                } else {
                    right.add(factory.concat(BigIntImmutable.create(entry.getValue().getBigInt().negate()),
                        factory.buildVariables(vars)));
                }
            }
        }
        return new Triple<GPoly<BigIntImmutable, GPolyVar>, GPoly<BigIntImmutable, GPolyVar>, Set<GPoly<BigIntImmutable, GPolyVar>>>(
            left.size() > 0 ? factory.plus(left) : factory.buildFromCoeff(((Ring<BigIntImmutable>) ring).zero()),
            right.size() > 0 ? factory.plus(right) : factory.buildFromCoeff(((Ring<BigIntImmutable>) ring).zero()),
            arbitraryConstantParts);
    }

    public int getInductionCounter() {
        return this.inductionCounter;
    }

    public ISMTChecker getSmtEngine() {
        return this.smtEngine;
    }

    @Override
    public String toString() {
        final StringBuilder b = new StringBuilder();
        b.append("NonInfConstraintGenerator:\nPathGenerator: ");
        b.append(this.pathGenerator);
        return b.toString();
    }

    protected static class NonInfConstraintGeneratorProof extends DefaultProof implements IConstraintGeneratorProof {

        private final InductionCalculusProof icProof;
        private final PolyAtom<BigIntImmutable> unsolvableConstraint;

        public NonInfConstraintGeneratorProof(final InductionCalculusProof icProof,
                final PolyAtom<BigIntImmutable> unsolvableConstraint) {
            this.icProof = icProof;
            this.unsolvableConstraint = unsolvableConstraint;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder result = new StringBuilder();
            result.append("The DP Problem is simplified using the Induction " + "Calculus " + o.cite(Citation.NONINF)
                + " with the following steps:");
            result.append(o.newline());
            result.append(this.icProof.export(o));
            if (this.unsolvableConstraint != null) {
                result.append(o.newline());
                result.append("The following constraint is trivially unsolvable: ");
                result.append(o.newline());
                result.append(this.unsolvableConstraint);
            }
            return result.toString();
        }

    }

    public static class Arguments {
        /**
         * Number of Inductions per Equality.
         */
        public int inductionCounter = 1;

        public int rewritingCounter = 20;

        public ISMTChecker smtEngine = new YicesChecker();;

        public IPathGenerator pathGenerator;

        public CondGPCToGPCTransformer.SearchMode uncondMode = CondGPCToGPCTransformer.SearchMode.P_LEQ_Q;

        public int dropOrientConditions = 0;
    }

}
