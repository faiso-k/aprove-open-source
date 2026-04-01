/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.DPConstraints.Predicate.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.IDPGInterpretation.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

public class InfRuleToPoly extends InfRuleConstraintRepl<Object> {

    protected static final BigInteger TWO = BigInteger.valueOf(2);

    public InfRuleToPoly() {
        super(Mode.Full);
    }

    @Override
    protected Constraint processConstraint(
        final Implication origImplication,
        final Constraint constraint,
        final boolean isConclusion,
        final Object data,
        final Abortion aborter) throws AbortionException
    {
        if (constraint.isReducesTo()) {
            return this.processReducesTo(origImplication, (ReducesTo) constraint, isConclusion, aborter);
        } else if (constraint.isPredicate()) {
            return this.processPredicate(origImplication, (Predicate) constraint, isConclusion, aborter);
        } else if (constraint.isPolyAtom()) {
            return constraint;
        } else if (constraint.isUsableAtom()) {
            return constraint;
        } else if (!isConclusion) {
            return null;
        }
        throw new UnsupportedOperationException("Unknown constraint type: " + constraint);
    }

    private Constraint processPredicate(
        final Implication origImplication,
        final Predicate predicate,
        final boolean isConclusion,
        final Abortion aborter) throws AbortionException
    {
        if (predicate.getKind() == Kind.AbstractRelation
            || predicate.getKind() == Kind.AbstractRelationEQ
            || predicate.getKind() == Kind.NonInfConstantCompare)
        {
            Constraint res;
            if (isConclusion) {
                res =
                    this.buildConclusionAtom(
                        predicate.getOrigRule(),
                        predicate.getLeft(),
                        predicate.getRight(),
                        predicate.getKind(),
                        origImplication,
                        predicate,
                        aborter);
            } else {
                res =
                    this.buildAtom(
                        predicate.getLeft(),
                        RelDependency.Wild,
                        null,
                        predicate.getRight(),
                        RelDependency.Wild,
                        null,
                        predicate.getKind() == Kind.AbstractRelationEQ ? ConstraintType.GE : ConstraintType.GT,
                        predicate,
                        aborter);
            }
            if (res != null) {
                return res;
            }
        }
        if (!isConclusion) {
            return null;
        } else {
            throw new UnsupportedOperationException("can not process conclusion: " + predicate);
        }
    }

    protected Constraint processReducesTo(
        final Implication origImplication,
        final ReducesTo reducesTo,
        final boolean isConclusion,
        final Abortion aborter) throws AbortionException
    {
        final IDPNonInfInterpretation interpretation = (IDPNonInfInterpretation) this.getIrc().getPolyInterpretation();
        final IDPPredefinedMap predefinedMap =
            ((IdpInductionCalculus) this.irc).getIdp().getRuleAnalysis().getPreDefinedMap();
        if (!interpretation.isNat()) {
            final Boolean boolRight = PredefinedSemanticsFactory.getBoolValue(reducesTo.getRight());
            // special treatment of something like s >= t = false
            // System.err.println("YEEHAH " + reducesTo.getRight() + " " + boolRight);
            if (boolRight != null) {
                if (!reducesTo.getLeft().isVariable()) {
                    final TRSFunctionApplication reduceLeft = ((TRSFunctionApplication) reducesTo.getLeft());
                    final FunctionSymbol reduceLeftRoot = reduceLeft.getRootSymbol();
                    final PredefinedFunction func = predefinedMap.getPredefinedFunction(reduceLeftRoot);
                    if (func != null) {
                        if (func.getFunc() == Func.Eq || func.getFunc() == Func.Neq) {
                            throw new UnsupportedOperationException("replace equality / inequality by ge, ge first!");
                        } else {
                            ConstraintType relation = null;
                            TRSTerm left = null;
                            TRSTerm right = null;
                            switch (func.getFunc()) {
                            case Gt:
                                relation = ConstraintType.GT;
                                left = reduceLeft.getArgument(0);
                                right = reduceLeft.getArgument(1);
                                break;
                            case Ge:
                                relation = ConstraintType.GE;
                                left = reduceLeft.getArgument(0);
                                right = reduceLeft.getArgument(1);
                                break;
                            case Lt:
                                relation = ConstraintType.GT;
                                left = reduceLeft.getArgument(1);
                                right = reduceLeft.getArgument(0);
                                break;
                            case Le:
                                relation = ConstraintType.GE;
                                left = reduceLeft.getArgument(1);
                                right = reduceLeft.getArgument(0);
                                break;
                            }
                            if (left != null
                                && right != null
                                && this.regardTerm(left, predefinedMap)
                                && this.regardTerm(right, predefinedMap))
                            {
                                if (relation != null) {
                                    if (!boolRight) {
                                        if (relation == ConstraintType.GT) {
                                            relation = ConstraintType.GE;
                                        } else {
                                            relation = ConstraintType.GT;
                                        }
                                        final TRSTerm tmpLeft = left;
                                        left = right;
                                        right = tmpLeft;
                                    }
                                    final RelDependency depLeft = RelDependency.Increasing;
                                    final RelDependency depRight = RelDependency.Decreasing;
                                    return this.buildAtom(
                                        left,
                                        depLeft,
                                        depLeft,
                                        right,
                                        depRight,
                                        depRight,
                                        relation,
                                        reducesTo,
                                        aborter);
                                }
                            }
                        }
                    }
                }
            }
        }
        Constraint res = null;
        {
            if (this.regardTerm(reducesTo.getLeft(), predefinedMap)) {
                res =
                    this.buildAtom(
                        reducesTo.getLeft(),
                        RelDependency.Increasing,
                        null,
                        reducesTo.getRight(),
                        RelDependency.Decreasing,
                        null,
                        ConstraintType.GE,
                        reducesTo,
                        aborter);
            }
        }
        if (res != null || !isConclusion) {
            return res;
        } else {
            throw new UnsupportedOperationException("can not process conclusion: " + reducesTo);
        }
    }

    protected Constraint hadleEquality(
        final TRSFunctionApplication reduceLeft,
        final Boolean boolRight,
        final ReducesTo reducesTo,
        final IDPPredefinedMap predefinedMap,
        final Abortion aborter) throws AbortionException
    {
        if (PredefinedUtil.onlyPredefined(reduceLeft.getArgument(0), predefinedMap)
            && PredefinedUtil.onlyPredefined(reduceLeft.getArgument(1), predefinedMap))
        {
            if (boolRight) {
                return ConstraintSet.flatCreate(
                    this.buildAtom(
                        reduceLeft.getArgument(0),
                        RelDependency.Increasing,
                        RelDependency.Increasing,
                        reduceLeft.getArgument(1),
                        RelDependency.Decreasing,
                        RelDependency.Decreasing,
                        ConstraintType.GE,
                        reducesTo,
                        aborter),
                    this.buildAtom(
                        reduceLeft.getArgument(1),
                        RelDependency.Increasing,
                        RelDependency.Increasing,
                        reduceLeft.getArgument(0),
                        RelDependency.Decreasing,
                        RelDependency.Decreasing,
                        ConstraintType.GE,
                        reducesTo,
                        aborter));
            } else {
                return ConstraintSet.flatCreate(
                    this.buildAtom(
                        reduceLeft.getArgument(0),
                        RelDependency.Increasing,
                        RelDependency.Increasing,
                        reduceLeft.getArgument(1),
                        RelDependency.Decreasing,
                        RelDependency.Decreasing,
                        ConstraintType.GE,
                        reducesTo,
                        aborter),
                    this.buildAtom(
                        reduceLeft.getArgument(1),
                        RelDependency.Increasing,
                        RelDependency.Increasing,
                        reduceLeft.getArgument(0),
                        RelDependency.Decreasing,
                        RelDependency.Decreasing,
                        ConstraintType.GE,
                        reducesTo,
                        aborter));
            }
        }
        return null;
    }

    protected boolean regardTerm(final TRSTerm t, final IDPPredefinedMap predefinedMap) {
        if (t.isVariable()) {
            return true;
        } else {
            return predefinedMap.isUndefinedInt(((TRSFunctionApplication) t).getRootSymbol())
                || PredefinedUtil.onlyPredefined(t, predefinedMap);
        }
    }

    protected Constraint buildAtom(
        final TRSTerm left,
        final RelDependency kLeft,
        final RelDependency uLeft,
        final TRSTerm right,
        final RelDependency kRight,
        final RelDependency uRight,
        ConstraintType relation,
        final TermAtom termAtom,
        final Abortion aborter) throws AbortionException
    {
        final IDPNonInfInterpretation interpretation = (IDPNonInfInterpretation) this.getIrc().getPolyInterpretation();
        OrderPoly<BigIntImmutable> leftPoly, rightPoly;
        leftPoly = interpretation.interpretTerm(left, kLeft, aborter);
        rightPoly = interpretation.interpretTerm(right, kRight, aborter);
        if (relation == ConstraintType.GT) {
            relation = ConstraintType.GE;
            rightPoly =
                interpretation.getFactory().plus(
                    rightPoly,
                    interpretation.getFactory().wrap(interpretation.getFactory().getFactory().one()));
        }
        final Set<Constraint> res = new LinkedHashSet<Constraint>();
        res.add(PolyAtom.create(
            interpretation.getFactory().minus(leftPoly, rightPoly),
            relation,
            interpretation,
            termAtom,
            left,
            right,
            0));
        if (uLeft != null && !left.isVariable() && !this.irc.isNormal(left)) {
            res.add(UsableAtom.create(left, ConstraintType.GE, uLeft, interpretation));
        }
        if (uRight != null && !right.isVariable() && !this.irc.isNormal(right)) {
            res.add(UsableAtom.create(right, ConstraintType.GE, uRight, interpretation));
        }
        return ConstraintSet.create(res);
    }

    protected Constraint buildConclusionAtom(
        final GeneralizedRule rule,
        final TRSTerm left,
        final TRSTerm right,
        final Kind kind,
        final Implication origImplication,
        final Predicate termAtom,
        final Abortion aborter) throws AbortionException
    {
        if (kind == Kind.AbstractRelationEQ) {
            return this.buildAtom(
                left,
                termAtom.getULeft(),
                termAtom.getULeft(),
                right,
                termAtom.getURight(),
                termAtom.getURight(),
                ConstraintType.GE,
                termAtom,
                aborter);
        }
        final IDPNonInfInterpretation interpretation = (IDPNonInfInterpretation) this.getIrc().getPolyInterpretation();
        if (kind == Kind.AbstractRelation) {
            final PolyAtom<BigIntImmutable> atom =
                PolyAtom.create(
                    interpretation.getFactory().minus(
                        interpretation.getFactory().minus(
                            interpretation.interpretTerm(left, termAtom.getULeft(), aborter),
                            interpretation.interpretTerm(right, termAtom.getURight(), aborter)),
                        interpretation.getFactory().buildFromCoeff(
                            interpretation.getBoolConstant(ConstantType.StrictOrientation, rule))),
                    ConstraintType.GE,
                    interpretation,
                    termAtom,
                    left,
                    right,
                    0);
            /*
            System.err.println("AbstractRelation ATOM: " + left + " > " + right);
            System.err.println(PolyAtom.create(interpretation.interpretTerm(left), ConstraintType.GE, interpretation, termAtom));
            System.err.println(PolyAtom.create(interpretation.interpretTerm(right), ConstraintType.GE, interpretation, termAtom));
            System.err.println(PolyAtom.create(interpretation.getFactory().getFactory().buildFromCoeff(interpretation.getBoolConstant(ConstantType.StrictOrientation, rule)), ConstraintType.GE, interpretation, termAtom));
            System.err.println(atom);
            */
            return atom;
        } else if (kind == Kind.NonInfConstantCompare) {
            if (origImplication.getConditions().isEmpty()) {
                // do not try to bound without pre-conditions
                interpretation.setBoolConstantValue(
                    ConstantType.CompareToNonInfConstant,
                    termAtom.getOrigRule(),
                    BigIntImmutable.ZERO);
                final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> poly =
                    interpretation
                        .getFactory()
                        .buildFromCoeff(
                            interpretation.getBoolConstantVar(
                                ConstantType.CompareToNonInfConstant,
                                termAtom.getOrigRule()));
                return PolyAtom.create(poly, ConstraintType.EQ, interpretation, termAtom, termAtom.getLeft(), null, 0);
            } else {
                // GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> poly = interpretation.getFactory().minus(interpretation.interpretTerm(left, RelDependency.Decreasing), interpretation.getNonInfBoundPoly());
                final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> poly =
                    interpretation.getFactory().times(
                        interpretation.getFactory().minus(
                            interpretation.interpretTerm(left, RelDependency.Decreasing, aborter),
                            interpretation.getNonInfBoundPoly()),
                        interpretation
                            .getFactory()
                            .buildFromCoeff(
                                interpretation.getBoolConstant(
                                    ConstantType.CompareToNonInfConstant,
                                    termAtom.getOrigRule())));
                return PolyAtom.create(poly, ConstraintType.GE, interpretation, termAtom, termAtom.getLeft(), null, 0);
            }
        } else {
            throw new UnsupportedOperationException("unsupported kind");
        }
    }

    /*
    Set<FunctionSymbol> symbolsLeft = reducesTo.getLeft().getFunctionSymbols();
    boolean ok = true;
    for (FunctionSymbol fs : symbolsLeft) {
        if (!PredefinedFunctions.isPredefined(fs) || !PredefinedFunctions.getFunction(fs).isArithmetic() || !hasZDomain(fs)) {
            ok = false;
            break;
        }
    }
    if (ok) {

    }
    protected boolean hasZDomain(FunctionSymbol fs) {
        List<Domain> domains = PredefinedFunctions.getSuffixList(fs);
        for (Domain domain : domains) {
            if (domain != DomainFactory.Z) {
                return false;
            }
        }
        return true;
    }
    */

    @Override
    public InfRuleID getID() {
        return InfRuleID.POLY_CONSTRAINTS;
    }

    @Override
    public String getLongName() {
        return "Rule Poly";
    }

    @Override
    public String getName() {
        return "Rule Poly: convert from terms to polynomial interpretations";
    }

    @Override
    protected Object prepare(final Implication implication, final Abortion aborter) {
        // TODO Auto-generated method stub
        return null;
    }

}
