/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class NatOPCSimplifyer<C extends GPolyCoeff> {

    private final FlatteningVisitor<C, GPolyVar> fvInner;
    private final OrderPolyFactory<C> orderPolyFactory;
    private final ConstraintFactory<C> constraintFactory;
    private int orLevel = 0;
    private int notLevel = 0;


    public NatOPCSimplifyer(final FlatteningVisitor <C, GPolyVar> fvInner,
            final OrderPolyFactory<C> orderPolyFactory,
            final ConstraintFactory<C> constraintFactory) {
        this.constraintFactory = constraintFactory;
        this.orderPolyFactory = orderPolyFactory;
        this.fvInner = fvInner;
    }


    public OrderPolyConstraint<C> simplify(OrderPolyConstraint<C> constraint, Map<GPolyVar, C> values) {
        SimplifyVisitor<C> visitor = new SimplifyVisitor<C>(this.fvInner, this.orderPolyFactory.getInnerFactory(), this.orderPolyFactory, this.constraintFactory, values);
        int oldSize;
        do {
            oldSize = values.size();
            constraint = visitor.applyToWithCleanup(constraint);
        } while (values.size() != oldSize);
        return constraint;
    }

    protected class SimplifyVisitor<D extends GPolyCoeff> extends ConstraintVisitor.ConstraintVisitorSkeleton<D> {

        private final GPolyFactory<D, GPolyVar> factory;
        private final FlatteningVisitor<D, GPolyVar> fvInner;
        private final Pair<Semiring<D>, CMonoid<GMonomial<GPolyVar>>> innerRingMonoid;
        private final Map<GPolyVar, D> values;
        private final OrderPolyFactory<D> orderPolyFactory;
        private final ConstraintFactory<D> constraintFactory;

        public SimplifyVisitor(final FlatteningVisitor <D, GPolyVar> fvInner,
                final GPolyFactory<D, GPolyVar> factory,
                final OrderPolyFactory<D> orderPolyFactory,
                final ConstraintFactory<D> constraintFactory,
                final Map<GPolyVar, D> values) {
            this.factory = factory;
            this.constraintFactory = constraintFactory;
            this.orderPolyFactory = orderPolyFactory;
            this.fvInner = fvInner;
            this.innerRingMonoid = new Pair<Semiring<D>, CMonoid<GMonomial<GPolyVar>>>(fvInner.getRingC(), fvInner.getMonoid());
            this.values = values;
        }

        /**
         * An atom is being visited.
         * @param param The constraint.
         * @return Some new constraint.
         */
        @Override
        public OrderPolyConstraint<D> caseAtom(final OPCAtom<D> param) {
            GPoly<D, GPolyVar> newLeft = this.simplifyPoly(param.getLeftPoly().getInnerPoly());
            GPoly<D, GPolyVar> newRight = null;
            if (param.getRightPoly() != null) {
                newRight = this.simplifyPoly(param.getRightPoly().getInnerPoly());
            }
            if (newRight == null) {
                if (param.getConstraintType() == ConstraintType.GE) {
                    return this.constraintFactory.createTrue();
                } else if (param.getConstraintType() == ConstraintType.GT) {
                    return this.constraintFactory.createTrue();
                }
            }
            if (newLeft == null) {
                if (param.getConstraintType() == ConstraintType.GT) {
                    return this.constraintFactory.createFalse();
                }
                /*
                if (!newRight.isFlat(innerRingMonoid)) {
                    fvInner.applyTo(newRight);
                }
                ImmutableMap<GMonomial<GPolyVar>, D> monomials = newRight.getMonomials(innerRingMonoid);
                for (Map.Entry<GMonomial<GPolyVar>, D> monomial : monomials.entrySet()) {
                    Map<GPolyVar, BigInteger> exp = monomial.getKey().getExponents();
                    if (exp.size() == 1) {
                        values.put(exp.keySet().iterator().next(), innerRingMonoid.x.zero());
                    }
                }
                newLeft = factory.one();*/
                newLeft = this.factory.zero();
            }
            return new OPCAtom<D>(this.orderPolyFactory.buildFromCoeff(newLeft),
                    newRight != null ? this.orderPolyFactory.buildFromCoeff(newRight) : null, param.getConstraintType());
        }

        protected GPoly<D, GPolyVar> simplifyPoly(GPoly<D, GPolyVar> poly) {
            if (!poly.isFlat(this.innerRingMonoid)) {
                this.fvInner.applyTo(poly);
            }
            ImmutableMap<GMonomial<GPolyVar>, D> monomials = poly.getMonomials(this.innerRingMonoid);
            GPoly<D, GPolyVar> res = null;
            outer : for (Map.Entry<GMonomial<GPolyVar>, D> monomial : monomials.entrySet()) {
                D coeff = monomial.getValue();
                if (this.innerRingMonoid.x.zero().equals(coeff)) {
                    continue;
                }
                Collection<GPolyVar> vars = new ArrayList<GPolyVar>();
                for (Map.Entry<GPolyVar, BigInteger> varEntry : monomial.getKey().getExponents().entrySet()) {
                    GPolyVar var = varEntry.getKey();
                    if (this.values.containsKey(var)) {
                        D value = this.values.get(var);
                        if (this.innerRingMonoid.x.zero().equals(value)) {
                            continue outer;
                        }
                        for (int i = varEntry.getValue().intValue()-1; i >= 0; i--) {
                            this.innerRingMonoid.x.times(coeff, value);
                        }
                    } else {
                        for (int i = varEntry.getValue().intValue()-1; i >= 0; i--) {
                            vars.add(var);
                        }
                    }
                }
                if (res == null) {
                    res = this.factory.concat(coeff, this.factory.buildVariables(vars));
                } else {
                    res = this.factory.plus(res, this.factory.concat(coeff, this.factory.buildVariables(vars)));
                }
            }
            return res;
        }

        // avoid exception
        @Override
        public void fcaseLogVar(OPCLogVar<D> param) {
        }

        @Override
        public void fcaseOr(
                final OPCOr<D> param) {
            NatOPCSimplifyer.this.orLevel++;
            super.fcaseOr(param);
        }

        @Override
        public OrderPolyConstraint<D> caseOr(
                final OPCOr<D> param,
                final Set<OrderPolyConstraint<D>> newOperands) {
            if (newOperands.contains(OPCTrue.<D>getTrue())) {
                return OPCTrue.<D>getTrue();
            }
            newOperands.remove(OPCFalse.<D>getFalse());
            NatOPCSimplifyer.this.orLevel--;
            if (newOperands.isEmpty()) {
                return OPCFalse.<D>getFalse();
            } else if (newOperands.size() == 1) {
                return newOperands.iterator().next();
            } else {
                return super.caseOr(param, newOperands);
            }
        }

        @Override
        public OrderPolyConstraint<D> caseAnd(
                final OPCAnd<D> param,
                final Set<OrderPolyConstraint<D>> newOperands) {
            if (newOperands.contains(OPCFalse.<D>getFalse())) {
                return OPCFalse.<D>getFalse();
            }
            newOperands.remove(OPCTrue.<D>getTrue());
            if (newOperands.isEmpty()) {
                return OPCTrue.<D>getTrue();
            } else if (newOperands.size() == 1) {
                return newOperands.iterator().next();
            } else {
                return super.caseAnd(param, newOperands);
            }
        }

        /**
         * An existential quantifier constraint is being visited.
         * @param param The constraint.
         * @param newConstraint The (new?) subconstraint.
         * @return Some new constraint.
         */
        @Override
        public OrderPolyConstraint<D> caseQuantifierE(
                final OPCQuantifierE<D> param,
                final OrderPolyConstraint<D> newConstraint) {
            if (newConstraint.equals(OPCTrue.<D>getTrue())) {
                return OPCTrue.<D>getTrue();
            }  else if (newConstraint.equals(OPCFalse.<D>getFalse())) {
                return OPCFalse.<D>getFalse();
            }
            return super.caseQuantifierE(param, newConstraint);
        }
        /**
         * A universal quantifier constraint is being visited.
         * @param param The constraint.
         * @param newConstraint The (new?) subconstraint.
         * @return Some new constraint.
         */
        @Override
        public OrderPolyConstraint<D> caseQuantifierA(
                final OPCQuantifierA<D> param,
                final OrderPolyConstraint<D> newConstraint) {
            if (newConstraint.equals(OPCTrue.<D>getTrue())) {
                return OPCTrue.<D>getTrue();
            }  else if (newConstraint.equals(OPCFalse.<D>getFalse())) {
                return OPCFalse.<D>getFalse();
            }
            return super.caseQuantifierA(param, newConstraint);
        }

        @Override
        public void fcaseNot(
                final OPCNot<D> param) {
            NatOPCSimplifyer.this.notLevel++;
            super.fcaseNot(param);
        }

        @Override
        public OrderPolyConstraint<D> caseNot(final OPCNot<D> param,
                final OrderPolyConstraint<D> newConstraint) {
            NatOPCSimplifyer.this.notLevel--;
            return super.caseNot(param, newConstraint);
        }

    }

}
