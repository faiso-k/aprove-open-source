package aprove.verification.complexity.TruthValue;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.MinMaxExprs.*;
import aprove.verification.oldframework.Logic.*;

public class FixedDegreePoly extends ComplexityValue {

    private final int degree;

    public int getDegree() {
        return this.degree;
    }

    protected FixedDegreePoly(final int degree, Optional<MinMaxExpr> concreteValue) {
        super(Order.FIXED_DEGREE_POLY, concreteValue);
        if (degree <= 0) {
            throw new IllegalArgumentException();
        }
        this.degree = degree;
    }

    @Override
    public int innerCompareTo(final ComplexityValue other) {
        final FixedDegreePoly fdpOther = (FixedDegreePoly) other;
        int c = this.degree - fdpOther.degree;
        if (c != 0) return c;
        return super.innerCompareTo(other);
    }

    @Override
    public YNM fallbackToYNM() {
        return YNM.YES;
    }

    @Override
    public boolean isPoly(int degree) {
        return this.degree == degree;
    }

    public boolean isCompletelyKnown() {
        return true;
    }

    public ComplexityValue multiply(final FixedDegreePoly other) {
        return ComplexityValue.fixedDegreePoly(this.degree + other.degree);
    }

    @Override
    public String export(Export_Util eu, String landauSign) {
        return landauSign + eu.escape("(") + export(eu) + eu.escape(")");
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + degree;
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (!super.equals(obj))
            return false;
        if (getClass() != obj.getClass())
            return false;
        FixedDegreePoly other = (FixedDegreePoly) obj;
        if (degree != other.degree)
            return false;
        return true;
    }

    @Override
    ComplexityValue withConcreteValue(Optional<MinMaxExpr> concreteVale) {
        return new FixedDegreePoly(degree, concreteVale);
    }

    @Override
    public String export(Export_Util eu) {
        return eu.escape("n") + eu.sup(eu.escape(Integer.toString(degree)));
    }

}
