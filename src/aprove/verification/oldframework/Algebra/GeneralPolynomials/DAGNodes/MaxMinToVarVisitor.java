/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class MaxMinToVarVisitor<C extends GPolyCoeff> extends GPolyVisitor<GPoly<C, GPolyVar>, GPolyVar> {

    private final Map<GPolyVar, GPolyVar> cache;
    private final GPolyFactory<GPoly<C, GPolyVar>, GPolyVar> factory;
    private final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter;
    private final FlatteningVisitor<C, GPolyVar> fvInner;
    private final Pair<Semiring<GPoly<C, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>> outerRingMonoid;
    private final Pair<Semiring<C>, CMonoid<GMonomial<GPolyVar>>> innerRingMonoid;

    public MaxMinToVarVisitor(final FlatteningVisitor <C, GPolyVar> fvInner,
            final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter,
            final GPolyFactory<GPoly<C, GPolyVar>, GPolyVar> factory) {
        this.cache = new HashMap<GPolyVar, GPolyVar>();
        this.factory = factory;
        this.fvInner = fvInner;
        this.fvOuter = fvOuter;
        this.outerRingMonoid = new Pair<Semiring<GPoly<C, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>>(fvOuter.getRingC(), fvOuter.getMonoid());
        this.innerRingMonoid = new Pair<Semiring<C>, CMonoid<GMonomial<GPolyVar>>>(fvInner.getRingC(), fvInner.getMonoid());
    }

    @Override
    public void fcaseMinNode(MinNode m) {

    }

    @Override
    public void fcaseMaxNode(MaxNode m) {
    }

    @Override
    public GPoly<GPoly<C, GPolyVar>, GPolyVar> caseMaxNode(
            final MaxNode<GPoly<C, GPolyVar>, GPolyVar> m,
            final GPoly<GPoly<C, GPolyVar>, GPolyVar> left,
            final GPoly<GPoly<C, GPolyVar>, GPolyVar> right) {
        this.deepFlatten(left);
        this.deepFlatten(right);
        MaxVar<C> var = new MaxVar<C>(left, right, this.outerRingMonoid, this.fvInner, this.fvOuter);
        GPolyVar cached = this.cache.get(var);
        if (cached == null) {
            cached = var;
            this.cache.put(var, var);
        }
        return this.factory.buildFromVariable(cached);
    }

    @Override
    public GPoly<GPoly<C, GPolyVar>, GPolyVar> caseMinNode(
            final MinNode<GPoly<C, GPolyVar>, GPolyVar> m,
            final GPoly<GPoly<C, GPolyVar>, GPolyVar> left,
            final GPoly<GPoly<C, GPolyVar>, GPolyVar> right) {
        this.deepFlatten(left);
        this.deepFlatten(right);
        MinVar<C> var = new MinVar<C>(left, right, this.outerRingMonoid, this.fvInner, this.fvOuter);
        GPolyVar cached = this.cache.get(var);
        if (cached == null) {
            cached = var;
            this.cache.put(var, var);
        }
        return this.factory.buildFromVariable(cached);
    }

    protected GPoly<GPoly<C, GPolyVar>, GPolyVar> deepFlatten(GPoly<GPoly<C, GPolyVar>, GPolyVar> poly) {
        if (!poly.isFlat(this.fvOuter.getRingC(), this.fvOuter.getMonoid())) {
            poly = this.fvOuter.applyTo(poly);
        }
        Map<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> monoms =
            poly.getMonomials(this.outerRingMonoid);
        for (GPoly<C, GPolyVar> innerPoly : monoms.values()) {
            if (!innerPoly.isFlat(this.innerRingMonoid)) {
                this.fvInner.applyTo(innerPoly);
            }
        }
        return poly;
    }

    @Override
    public GPoly<GPoly<C, GPolyVar>, GPolyVar> casePlusNode(
            final PlusNode<GPoly<C, GPolyVar>, GPolyVar> p,
            final GPoly<GPoly<C, GPolyVar>, GPolyVar> left,
            final GPoly<GPoly<C, GPolyVar>, GPolyVar> right) {
        if (p.getLeft() == left && p.getRight() == right) {
            return p;
        } else {
            return this.factory.plus(left, right);
        }
    }

    @Override
    public GPoly<GPoly<C, GPolyVar>, GPolyVar> caseMinusNode(
            final MinusNode<GPoly<C, GPolyVar>, GPolyVar> m,
            final GPoly<GPoly<C, GPolyVar>, GPolyVar> left,
            final GPoly<GPoly<C, GPolyVar>, GPolyVar> right) {
        if (m.getLeft() == left && m.getRight() == right) {
            return m;
        } else {
            return this.factory.minus(left, right);
        }
    }

    @Override
    public GPoly<GPoly<C, GPolyVar>, GPolyVar> caseTimesNode(
            final TimesNode<GPoly<C, GPolyVar>, GPolyVar> t,
            final GPoly<GPoly<C, GPolyVar>, GPolyVar> left,
            final GPoly<GPoly<C, GPolyVar>, GPolyVar> right) {
        if (t.getLeft() == left && t.getRight() == right) {
            return t;
        } else {
            return this.factory.times(left, right);
        }
    }


    public static class MaxVar<C extends GPolyCoeff> extends MaxNode<GPoly<C, GPolyVar>, GPolyVar> implements GPolyVar {

        private final Pair<Semiring<GPoly<C, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>> ringMonoid;
        private final FlatteningVisitor<C, GPolyVar> fvInner;
        private final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter;

        MaxVar(final GPoly<GPoly<C, GPolyVar>, GPolyVar> leftParam,
                final GPoly<GPoly<C, GPolyVar>, GPolyVar> rightParam,
                final Pair<Semiring<GPoly<C, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>> ringMonoid,
                final FlatteningVisitor <C, GPolyVar> fvInner,
                final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter) {
            super(leftParam, rightParam);
            this.ringMonoid = ringMonoid;
            this.fvInner = fvInner;
            this.fvOuter = fvOuter;
        }

        @Override
        public String getName() {
            return this.export(new PLAIN_Util());
        }

        @Override
        public String export(Export_Util eu) {
            StringBuilder sb = new StringBuilder();
            sb.append("max{");
            sb.append(new OrderPoly<C>(this.left).exportFlatDeep(this.fvInner, this.fvOuter, eu));
            sb.append(", ");
            sb.append(new OrderPoly<C>(this.right).exportFlatDeep(this.fvInner, this.fvOuter, eu));
            sb.append("}");
            return sb.toString();
        }

        @Override
        public boolean isAffected(Collection<? extends GPolyVar> vars) {
            ImmutableSet<GPolyVar> leftVars = this.left.getVariables();
            ImmutableSet<GPolyVar> rightVars = this.right.getVariables();
            for (GPolyVar var  : vars) {
                if (leftVars.contains(var) || rightVars.contains(var)) {
                    return true;
                }
            }
            return false;
        }

        @Override
        public <A extends GPolyCoeff, B extends GPolyVar> GPoly<A, B> replace(
                Map<B, ? extends GPoly<A, B>> replacement) {
            throw new UnsupportedOperationException();
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + this.left.getMonomials(this.ringMonoid).hashCode();
            result = prime * result + this.right.getMonomials(this.ringMonoid).hashCode();
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (this.getClass() != obj.getClass()) {
                return false;
            }
            final MaxVar<C> other = (MaxVar<C>) obj;
            if ((!this.left.getMonomials(this.ringMonoid).equals(other.left.getMonomials(this.ringMonoid))
                    && !this.left.getMonomials(this.ringMonoid).equals(other.right.getMonomials(this.ringMonoid)))
                        || (!this.right.getMonomials(this.ringMonoid).equals(other.right.getMonomials(this.ringMonoid))
                            && !this.right.getMonomials(this.ringMonoid).equals(other.left.getMonomials(this.ringMonoid)))) {
                return false;
            }
            return true;
        }
    }

    public static class MinVar<C extends GPolyCoeff> extends MaxNode<GPoly<C, GPolyVar>, GPolyVar> implements GPolyVar {

        private final Pair<Semiring<GPoly<C, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>> ringMonoid;
        private final FlatteningVisitor<C, GPolyVar> fvInner;
        private final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter;

        MinVar(final GPoly<GPoly<C, GPolyVar>, GPolyVar> leftParam,
                final GPoly<GPoly<C, GPolyVar>, GPolyVar> rightParam,
                final Pair<Semiring<GPoly<C, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>> ringMonoid,
                final FlatteningVisitor <C, GPolyVar> fvInner,
                final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter) {
            super(leftParam, rightParam);
            this.ringMonoid = ringMonoid;
            this.fvInner = fvInner;
            this.fvOuter = fvOuter;
        }

        @Override
        public String getName() {
            return this.export(new PLAIN_Util());
        }

        @Override
        public String export(Export_Util eu) {
            StringBuilder sb = new StringBuilder();
            sb.append("min{");
            sb.append(new OrderPoly<C>(this.left).exportFlatDeep(this.fvInner, this.fvOuter, eu));
            sb.append(", ");
            sb.append(new OrderPoly<C>(this.right).exportFlatDeep(this.fvInner, this.fvOuter, eu));
            sb.append("}");
            return sb.toString();
        }

        @Override
        public boolean isAffected(Collection<? extends GPolyVar> vars) {
            ImmutableSet<GPolyVar> leftVars = this.left.getVariables();
            ImmutableSet<GPolyVar> rightVars = this.right.getVariables();
            for (GPolyVar var  : vars) {
                if (leftVars.contains(var) || rightVars.contains(var)) {
                    return true;
                }
            }
            return false;
        }

        @Override
        public <A extends GPolyCoeff, B extends GPolyVar> GPoly<A, B> replace(
                Map<B, ? extends GPoly<A, B>> replacement) {
            throw new UnsupportedOperationException();
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 2;
            result = prime * result + this.left.getMonomials(this.ringMonoid).hashCode();
            result = prime * result + this.right.getMonomials(this.ringMonoid).hashCode();
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (this.getClass() != obj.getClass()) {
                return false;
            }
            final MinVar<C> other = (MinVar<C>) obj;
            if ((!this.left.getMonomials(this.ringMonoid).equals(other.left.getMonomials(this.ringMonoid))
                    && !this.left.getMonomials(this.ringMonoid).equals(other.right.getMonomials(this.ringMonoid)))
                        || (!this.right.getMonomials(this.ringMonoid).equals(other.right.getMonomials(this.ringMonoid))
                            && !this.right.getMonomials(this.ringMonoid).equals(other.left.getMonomials(this.ringMonoid)))) {
                return false;
            }
            return true;
        }
    }
}



