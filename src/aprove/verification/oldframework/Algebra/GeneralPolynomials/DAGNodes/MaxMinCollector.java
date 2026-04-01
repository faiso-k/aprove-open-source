/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.idp.*;
import aprove.verification.dpframework.DPProblem.SMT_LIA.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class MaxMinCollector extends GPolyVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> {

    // pair.y = conditions, pair.y = values
    // stack is build during traversal of node structore
    private final Stack<ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>>> stack;
    private final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> factory;
    private final FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> fvInner;
    private final GInterpretation<BigIntImmutable> interpretation;
    private final ISMTChecker smtEngine;
    private Set<PolyAtom<BigIntImmutable>> preconds;
    private Set<PolyAtom<BigIntImmutable>> linPreconds;
    private final Abortion aborter;

    public MaxMinCollector(GInterpretation<BigIntImmutable> gInterpretation, ISMTChecker smtEngine, Abortion aborter) {
        this.interpretation = gInterpretation;
        this.stack = new Stack<ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>>>();
        this.factory = gInterpretation.getFactory().getFactory();
        this.fvInner = gInterpretation.getFvOuter();
        this.smtEngine = smtEngine;
        this.aborter = aborter;
   }


    public GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> applyTo(final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> visitable, Set<PolyAtom<BigIntImmutable>> preconditions) {
        this.preconds = new LinkedHashSet<PolyAtom<BigIntImmutable>>();
        this.linPreconds = new LinkedHashSet<PolyAtom<BigIntImmutable>>();
        for (PolyAtom<BigIntImmutable> poly : preconditions) {
            if (poly.isLinear()) {
                this.linPreconds.add(poly);
            } else {
                this.preconds.add(poly);
            }
        }
        return visitable.visit(this);
    }

    public GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> applyTo(final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> visitable, Set<PolyAtom<BigIntImmutable>> linPreconditions, Set<PolyAtom<BigIntImmutable>> preconditions) {
        this.linPreconds = linPreconditions;
        this.preconds = preconditions;
        return visitable.visit(this);
    }


    @Override
    @Deprecated
    public GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> applyTo(final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> visitable) {
        return visitable.visit(this);
    }


    public void clearStack() {
        this.stack.clear();
        this.preconds = null;
        this.linPreconds = null;
    }

    public ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>> getValues() {
        if (aprove.Globals.useAssertions) {
            assert (this.stack.size() == 1) : "you must apply me first";
        }
        return this.stack.get(0);
    }

    // avoid unsupported operation exception
    @Override
    public void fcaseMinNode(
            final MinNode<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> t) {
    }

    // avoid unsupported operation exception
    @Override
    public void fcaseMaxNode(
            final MaxNode<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> t) {
    }

    /**
     * A minimum node is being visited. This is called after the children were
     * visited.
     * @param m Some MinNode.
     * @param left The possibly new left node.
     * @param right The possibly new right node.
     * @return Some new node depending on the visitor.
     */
    @Override
    public GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> caseMinNode(
            final MinNode<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> m,
            final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> left,
            final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> right) {
        ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>> rightValues = this.stack.pop();
        ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>> leftValues = this.stack.pop();
        ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>> newValues = new ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>>(leftValues.size() * rightValues.size());
        for (Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>> leftValue : leftValues) {
            for (Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>> rightValue : rightValues) {
                PolyAtom<BigIntImmutable> leftCond = PolyAtom.create(this.factory.minus(this.factory.minus(rightValue.z, leftValue.z), this.factory.one()), ConstraintType.GE, this.interpretation, null, null, null, 1);
                PolyAtom<BigIntImmutable> rightCond = PolyAtom.create(this.factory.minus(leftValue.z, rightValue.z), ConstraintType.GE, this.interpretation, null, null, null, 1);

                boolean leftLinear = leftCond.isLinear();
                boolean rightLinear = rightCond.isLinear();

                Set<PolyAtom<BigIntImmutable>> newConditions;
                if (leftValue.y.isEmpty()) {
                    newConditions = rightValue.y;
                } else if (rightValue.y.isEmpty()) {
                    newConditions = leftValue.y;
                } else {
                    newConditions = new LinkedHashSet<PolyAtom<BigIntImmutable>>(leftValue.y);
                    if (!this.addAllSat(newConditions, rightValue.y)) {
                        continue;
                    }
                }

                Set<PolyAtom<BigIntImmutable>> newLinConditions;
                if (leftValue.x.isEmpty()) {
                    newLinConditions = rightValue.x;
                } else if (rightValue.x.isEmpty()) {
                    newLinConditions = leftValue.x;
                } else {
                    newLinConditions = new LinkedHashSet<PolyAtom<BigIntImmutable>>(leftValue.x);
                    this.addAll(newLinConditions, rightValue.x);
                }

                Set<PolyAtom<BigIntImmutable>> newConditionsLeft = null;
                Set<PolyAtom<BigIntImmutable>> newConditionsRight = null;
                Set<PolyAtom<BigIntImmutable>> newLinConditionsLeft = null;
                Set<PolyAtom<BigIntImmutable>> newLinConditionsRight = null;

                if (leftLinear) {
                    newConditionsLeft = newConditions;
                    newLinConditionsLeft = new LinkedHashSet<PolyAtom<BigIntImmutable>>(newLinConditions);
                    if (!this.containsPoly(newLinConditionsLeft, leftCond)) {
                        newLinConditionsLeft.add(leftCond);
                    }
                } else {
                    if (this.isSatisfiableAfterAdd(newConditions, leftCond)) {
                        newConditionsLeft = new LinkedHashSet<PolyAtom<BigIntImmutable>>(newConditions);
                        if (!this.containsPoly(newConditionsLeft, leftCond)) {
                            newConditionsLeft.add(leftCond);
                        }
                        newLinConditionsLeft = newLinConditions;
                    }
                }

                if (newLinConditionsLeft != null && this.isSatisfiable(newLinConditionsLeft)) {
                    // left >= right <-> left - right >= 0
                    newValues.add(new Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>(newLinConditionsLeft, newConditionsLeft, leftValue.z));
                }

                if (rightLinear) {
                    newConditionsRight = leftLinear ? new LinkedHashSet<PolyAtom<BigIntImmutable>>(newConditions) : newConditions;
                    newLinConditionsRight = leftLinear ? newLinConditions : new LinkedHashSet<PolyAtom<BigIntImmutable>>(newLinConditions);
                    if (!this.containsPoly(newLinConditionsRight, rightCond)) {
                        newLinConditionsRight.add(rightCond);
                    }
                } else {
                    if (this.isSatisfiableAfterAdd(newConditions, rightCond)) {
                        newConditionsRight = leftLinear ? new LinkedHashSet<PolyAtom<BigIntImmutable>>(newConditions) : newConditions;
                        if (!this.containsPoly(newConditionsRight, rightCond)) {
                            newConditionsRight.add(rightCond);
                        }
                        newLinConditionsRight = leftLinear ? newLinConditions : new LinkedHashSet<PolyAtom<BigIntImmutable>>(newLinConditions);
                    }
                }

                if (newLinConditionsRight != null && this.isSatisfiable(newLinConditionsRight)) {
                    //  right > left <-> right - left -1 >= 0
                    newValues.add(new Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>(newLinConditionsRight, newConditionsRight, rightValue.z));
                }
            }
        }
        this.stack.add(newValues);
        return m;
    }

    protected boolean addAllSat(Set<PolyAtom<BigIntImmutable>> set, Set<PolyAtom<BigIntImmutable>> add) {
        List<PolyAtom<BigIntImmutable>> toAdd = new ArrayList<PolyAtom<BigIntImmutable>>(add.size());
        for (PolyAtom<BigIntImmutable> a : add) {
            if (!this.containsPoly(set, a)) {
                if (add.size() <= 1 || add.size() == 1 || this.isSatisfiableAfterAdd(set, a)) {
                    toAdd.add(a);
                } else {
                    return false;
                }
            }
        }
        set.addAll(toAdd);
        return true;
    }

    protected boolean addAll(Set<PolyAtom<BigIntImmutable>> set, Set<PolyAtom<BigIntImmutable>> add) {
        List<PolyAtom<BigIntImmutable>> toAdd = new ArrayList<PolyAtom<BigIntImmutable>>(add.size());
        for (PolyAtom<BigIntImmutable> a : add) {
            if (!this.containsPoly(set, a)) {
                toAdd.add(a);
            }
        }
        set.addAll(toAdd);
        return true;
    }

    protected boolean containsPoly(Set<PolyAtom<BigIntImmutable>> set, PolyAtom<BigIntImmutable> poly) {
        if (set.contains(poly)) {
            return true;
        }
        for (PolyAtom<BigIntImmutable> other : set) {
            if (OrderPoly.equals(this.interpretation, poly.getLhs(), other.getLhs())) {
                return true;
            }
        }
        return false;
    }


    /**
     * A maximum node is being visited. This is called after the children were
     * visited.
     * @param m Some MaxNode.
     * @param left The possibly new left node.
     * @param right The possibly new right node.
     * @return Some new node depending on the visitor.
     */
    @Override
    public GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> caseMaxNode(
            final MaxNode<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> m,
            final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> left,
            final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> right) {
        ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>> rightValues = this.stack.pop();
        ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>> leftValues = this.stack.pop();
        ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>> newValues = new ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>>(leftValues.size() * rightValues.size());
        for (Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>> leftValue : leftValues) {
            for (Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>> rightValue : rightValues) {
                PolyAtom<BigIntImmutable> leftCond = PolyAtom.create(this.factory.minus(leftValue.z, rightValue.z), ConstraintType.GE, this.interpretation, null, null, null, 1);
                PolyAtom<BigIntImmutable> rightCond = PolyAtom.create(this.factory.minus(this.factory.minus(rightValue.z, leftValue.z), this.factory.one()), ConstraintType.GE, this.interpretation, null, null, null, 1);

                boolean leftLinear = leftCond.isLinear();
                boolean rightLinear = rightCond.isLinear();

                Set<PolyAtom<BigIntImmutable>> newConditions;
                if (leftValue.y.isEmpty()) {
                    newConditions = rightValue.y;
                } else if (rightValue.y.isEmpty()) {
                    newConditions = leftValue.y;
                } else {
                    newConditions = new LinkedHashSet<PolyAtom<BigIntImmutable>>(leftValue.y);
                    if (!this.addAllSat(newConditions, rightValue.y)) {
                        continue;
                    }
                }

                Set<PolyAtom<BigIntImmutable>> newLinConditions;
                if (leftValue.x.isEmpty()) {
                    newLinConditions = rightValue.x;
                } else if (rightValue.x.isEmpty()) {
                    newLinConditions = leftValue.x;
                } else {
                    newLinConditions = new LinkedHashSet<PolyAtom<BigIntImmutable>>(leftValue.x);
                    this.addAll(newLinConditions, rightValue.x);
                }

                Set<PolyAtom<BigIntImmutable>> newConditionsLeft = null;
                Set<PolyAtom<BigIntImmutable>> newConditionsRight = null;
                Set<PolyAtom<BigIntImmutable>> newLinConditionsLeft = null;
                Set<PolyAtom<BigIntImmutable>> newLinConditionsRight = null;

                if (leftLinear) {
                    newConditionsLeft = newConditions;
                    newLinConditionsLeft = new LinkedHashSet<PolyAtom<BigIntImmutable>>(newLinConditions);
                    if (!this.containsPoly(newLinConditionsLeft, leftCond)) {
                        newLinConditionsLeft.add(leftCond);
                    }
                } else {
                    if (this.isSatisfiableAfterAdd(newConditions, leftCond)) {
                        newConditionsLeft = new LinkedHashSet<PolyAtom<BigIntImmutable>>(newConditions);
                        if (!this.containsPoly(newConditionsLeft, leftCond)) {
                            newConditionsLeft.add(leftCond);
                        }
                        newLinConditionsLeft = newLinConditions;
                    }
                }

                if (newLinConditionsLeft != null && this.isSatisfiable(newLinConditionsLeft)) {
                    // left >= right <-> left - right >= 0
                    newValues.add(new Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>(newLinConditionsLeft, newConditionsLeft, leftValue.z));
                }

                if (rightLinear) {
                    newConditionsRight = leftLinear ? new LinkedHashSet<PolyAtom<BigIntImmutable>>(newConditions) : newConditions;
                    newLinConditionsRight = leftLinear ? newLinConditions : new LinkedHashSet<PolyAtom<BigIntImmutable>>(newLinConditions);
                    if (!this.containsPoly(newLinConditionsRight, rightCond)) {
                        newLinConditionsRight.add(rightCond);
                    }
                } else {
                    if (this.isSatisfiableAfterAdd(newConditions, rightCond)) {
                        newConditionsRight = leftLinear ? new LinkedHashSet<PolyAtom<BigIntImmutable>>(newConditions) : newConditions;
                        if (!this.containsPoly(newConditionsRight, rightCond)) {
                            newConditionsRight.add(rightCond);
                        }
                        newLinConditionsRight = leftLinear ? newLinConditions : new LinkedHashSet<PolyAtom<BigIntImmutable>>(newLinConditions);
                    }
                }

                if (newLinConditionsRight != null && this.isSatisfiable(newLinConditionsRight)) {
                    //  right > left <-> right - left -1 >= 0
                    newValues.add(new Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>(newLinConditionsRight, newConditionsRight, rightValue.z));
                }

            }
        }
        this.stack.add(newValues);
        return m;
    }

    private boolean isSatisfiableAfterAdd(Set<PolyAtom<BigIntImmutable>> nonLinConds, PolyAtom<BigIntImmutable> newCond) {
        GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> fac = this.interpretation.getFactory().getFactory();
        outer : for (PolyAtom<BigIntImmutable> cond : nonLinConds) {
            GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> sum = fac.plus(cond.getLhs(), newCond.getLhs());
            this.interpretation.getFvOuter().applyTo(sum);
            boolean isFalse = false;
            ImmutableMap<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> mons = sum.getMonomials(this.interpretation.getOuterRingMonoid());
            for (Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> mon : mons.entrySet()) {
                if (!mon.getValue().isFlat(this.interpretation.getInnerRingMonoid())) {
                    this.interpretation.getFvInner().applyTo(mon.getValue());
                }
                if (mon.getKey().getExponents().isEmpty()) {
                    BigInteger coeffConst = this.getCoeffConstantValue(mon.getValue());
                    if (coeffConst != null && coeffConst.compareTo(BigInteger.ZERO) < 0) {
                        isFalse = true;
                    }
                } else {
                    BigInteger coeffConst = this.getCoeffConstantValue(mon.getValue());
                    if (coeffConst == null || coeffConst.compareTo(BigInteger.ZERO) != 0) {
                        continue outer;
                    }
                }
            }
            if (isFalse) {
                return false;
            }
        }
        return true;
    }

    protected BigInteger getCoeffConstantValue(GPoly<BigIntImmutable, GPolyVar> coeff) {
        ImmutableMap<GMonomial<GPolyVar>, BigIntImmutable> mons = coeff.getMonomials(this.interpretation.getInnerRingMonoid());
        if (mons.size() != 1) {
            return null;
        }
        Map.Entry<GMonomial<GPolyVar>, BigIntImmutable> mon = mons.entrySet().iterator().next();
        if (!mon.getKey().getExponents().isEmpty()) {
            return null;
        }
        return mon.getValue().getBigInt();
    }

    private boolean isSatisfiable(Set<PolyAtom<BigIntImmutable>> linConds) {

        if (linConds.isEmpty()) {
            return true;
        }
        GPolyFactory<BigIntImmutable, GPolyVar> innerFac = this.interpretation.getFactory().getInnerFactory();
        List<ImmutableBoolOp<LIAConstraint>> constraints = new ArrayList<ImmutableBoolOp<LIAConstraint>>(linConds.size());
        // linears are flat
        for (PolyAtom<BigIntImmutable> poly : linConds) {
            GPoly<BigIntImmutable, GPolyVar> sum = null;
            for (Map.Entry<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> mon : poly.getLhs().getMonomials(this.interpretation.getOuterRingMonoid()).entrySet()) {
                Iterator<GPolyVar> iter = mon.getKey().getExponents().keySet().iterator();
                GPoly<BigIntImmutable, GPolyVar> monPoly;
                if (iter.hasNext()) {
                    monPoly = innerFac.concat(mon.getValue().getConstantPart(this.interpretation.getInnerRingMonoid()), innerFac.buildVariable(iter.next()));
                } else {
                    monPoly = mon.getValue();
                }
                if (sum == null) {
                    sum = monPoly;
                } else {
                    sum = innerFac.plus(sum, monPoly);
                }
            }
            constraints.add(ImmutableBoolOp.createAtom(new LIAConstraint(sum, this.interpretation.getFactory().getInnerFactory().zero(), ArithmeticRelation.GE )));
        }
        YNM solution;
        try {
            solution = this.smtEngine.isSatisfiable(ImmutableBoolOp.createConjunction(constraints), this.aborter);
        } catch (final AbortionException e) {
            solution = YNM.MAYBE;
        }
        return solution != YNM.NO;
    }


    @Override
    public GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> caseConcatNode(
            final ConcatNode<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> c) {
        ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>> res = new ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>>(1);
        res.add(new Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>(new LinkedHashSet<PolyAtom<BigIntImmutable>>(this.linPreconds), new LinkedHashSet<PolyAtom<BigIntImmutable>>(this.preconds), c));
        this.stack.add(res);
        return c;
    }

    @Override
    public GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> casePlusNode(
            final PlusNode<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> p,
            final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> left,
            final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> right) {
        this.binaryNode(p, left, right, new FactoryWrapper<GPoly<BigIntImmutable, GPolyVar>>(this.factory, NodeType.Plus));
        return p;
    }

    @Override
    public GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> caseMinusNode(
            final MinusNode<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> p,
            final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> left,
            final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> right) {
        this.binaryNode(p, left, right, new FactoryWrapper<GPoly<BigIntImmutable, GPolyVar>>(this.factory, NodeType.Minus));
        return p;
    }

    @Override
    public GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> caseTimesNode(
            final TimesNode<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> p,
            final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> left,
            final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> right) {
        this.binaryNode(p, left, right, new FactoryWrapper<GPoly<BigIntImmutable, GPolyVar>>(this.factory, NodeType.Times));
        return p;
    }

    /**
     * Pops the left and right value from stack and combines them via the given factoryWrapper f a new node is needed
     * @param p
     * @param left
     * @param right
     * @param factoryWrapper
     */
    public void binaryNode(
            final BinaryNode<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> n,
            final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> left,
            final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> right,
            FactoryWrapper<GPoly<BigIntImmutable, GPolyVar>> factoryWrapper) {
        ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>> rightValues = this.stack.pop();
        ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>> leftValues = this.stack.pop();
        ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>> newValues = new ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>>(leftValues.size() * rightValues.size());
        for (Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>> leftValue : leftValues) {
            for (Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>> rightValue : rightValues) {
                Set<PolyAtom<BigIntImmutable>> newConditons;
                if (leftValue.y.isEmpty()) {
                    newConditons = rightValue.y;
                } else if (rightValue.y.isEmpty()) {
                    newConditons = leftValue.y;
                } else {
                    newConditons = new LinkedHashSet<PolyAtom<BigIntImmutable>>(leftValue.y);
                    if (!this.addAllSat(newConditons, rightValue.y)) {
                        continue;
                    }
                }
                Set<PolyAtom<BigIntImmutable>> newLinConditons;
                if (leftValue.x.isEmpty()) {
                    newLinConditons = rightValue.x;
                } else if (rightValue.x.isEmpty()) {
                    newLinConditons = leftValue.x;
                } else {
                    newLinConditons = new LinkedHashSet<PolyAtom<BigIntImmutable>>(leftValue.x);
                    this.addAll(newLinConditons, rightValue.x);
                    if (rightValues.size() > 1 && leftValues.size() > 1 && !this.isSatisfiable(newLinConditons)) {
                        continue;
                    }
                }

                GPoly<GPoly<BigIntImmutable, GPolyVar>,GPolyVar> newValue;
                if (leftValue.z == left && rightValue.z == right) {
                    newValue = n;
                } else {
                    // System.err.println("NEW VALUE");
                    newValue = factoryWrapper.createBinary(leftValue.z, rightValue.z);
                }
                newValues.add(new Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>(newLinConditons, newConditons, newValue));
            }
        }
        this.stack.add(newValues);
    }

    protected static enum NodeType {
        Times, Plus, Minus
    }

    protected static class FactoryWrapper<C extends GPolyCoeff> {

        private final GPolyFactory<C, GPolyVar> factory;
        private final NodeType nodeType;

        public FactoryWrapper(final GPolyFactory<C, GPolyVar> factory, final NodeType nodeType) {
            this.factory = factory;
            this.nodeType = nodeType;
        }

        public GPoly<C, GPolyVar> createBinary(final GPoly<C, GPolyVar> left, final GPoly<C, GPolyVar> right) {
            switch (this.nodeType) {
            case Times : return this.factory.times(left, right);
            case Plus : return this.factory.plus(left, right);
            case Minus : return this.factory.minus(left, right);
            default : throw new IllegalArgumentException("node type not supported " + this.nodeType);
            }
        }

    }
}
