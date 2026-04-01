package aprove.verification.complexity.TruthValue;

import java.util.function.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.verification.oldframework.Logic.*;

public class ComplexityYNM implements TruthValue {

    @SuppressWarnings("serial")
    public static class NoPolynomialUpperBoundException extends Exception {}

    public static int degreeOfUpperBound(final TruthValue tv) throws NoPolynomialUpperBoundException {
        if (tv instanceof ComplexityYNM) {
            final ComplexityValue ub = ((ComplexityYNM) tv).getUpperBound();
            if (ub instanceof FixedDegreePoly) {
                return ((FixedDegreePoly) ub).getDegree();
            } else if (ub.isConstant()) {
                return 0;
            }
        }
        throw new NoPolynomialUpperBoundException();
    }

    public static final ComplexityYNM CONSTANT = ComplexityYNM.create(
        ComplexityValue.constant(),
        ComplexityValue.constant());
    public static final ComplexityYNM INFINITE = ComplexityYNM.create(
        ComplexityValue.infinite(),
        ComplexityValue.infinite());
    public static final ComplexityYNM MAYBE = ComplexityYNM.create(ComplexityValue.constant(), ComplexityValue.infinite());
    public static final TruthValue FINITE = ComplexityYNM.create(ComplexityValue.constant(), ComplexityValue.finite());

    private final ComplexityValue lowerBound;
    private final ComplexityValue upperBound;

    private ComplexityYNM(final ComplexityValue lb, final ComplexityValue ub) {
        if (lb.compareTo(ub) <= 0) {
            this.lowerBound = lb;
            this.upperBound = ub;
        } else {
            throw new IllegalArgumentException();
        }
    }

    @Override
    public boolean equals(final Object other) {
        if (other instanceof ComplexityYNM) {
            final ComplexityYNM o = (ComplexityYNM) other;
            return (this.lowerBound.equals(o.lowerBound) && this.upperBound.equals(o.upperBound));
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        return this.lowerBound.hashCode() + 1024 * this.upperBound.hashCode();
    }

    public static ComplexityYNM create(final ComplexityValue lower, final ComplexityValue upper) {
        return new ComplexityYNM(lower, upper);
    }

    public static ComplexityYNM createLower(final ComplexityValue bound) {
        return new ComplexityYNM(bound, ComplexityValue.infinite());
    }

    public static ComplexityYNM createUpper(final ComplexityValue bound) {
        return new ComplexityYNM(ComplexityValue.constant(), bound);
    }

    public static ComplexityYNM toComplexityYNM(final TruthValue other) {
        if (other == YNM.MAYBE) {
            return ComplexityYNM.MAYBE;
        } else if (other instanceof ComplexityYNM) {
            return (ComplexityYNM) other;
        }
        throw new InvalidTruthValueException(ComplexityYNM.class, other);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public TruthValue and(final TruthValue other) {
        final ComplexityYNM cOther = ComplexityYNM.toComplexityYNM(other);
        final ComplexityValue lower = this.lowerBound.min(cOther.lowerBound);
        final ComplexityValue upper = this.upperBound.max(cOther.upperBound);
        return ComplexityYNM.create(lower, upper);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean canGoTo(final TruthValue other) {
        if (!(other instanceof ComplexityYNM)) {
            return false;
        }
        final ComplexityYNM cOther = (ComplexityYNM) other;
        return (this.lowerBound.compareTo(cOther.lowerBound) <= 0 && this.upperBound.compareTo(cOther.upperBound) >= 0);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public TruthValue combine(final TruthValue other) {
        if (other instanceof ComplexityYNM) {
            ComplexityYNM that = (ComplexityYNM) other;
            ComplexityValue lower = this.lowerBound.approximateMax(that.lowerBound);
            ComplexityValue upper = this.upperBound.approximateMin(that.upperBound);
            return new ComplexityYNM(lower, upper);
        }
        if (other == YNM.MAYBE) {
            return this;
        } else if (this.canGoTo(other)) {
            return other;
        } else if (other.canGoTo(this)) {
            return this;
        } else {
            throw new CombineException();
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public YNM fallbackToYNM() {
        if (this.upperBound.fallbackToYNM() == YNM.YES) {
            return YNM.YES;
        } else if (this.lowerBound.fallbackToYNM() == YNM.NO) {
            return YNM.NO;
        } else {
            return YNM.MAYBE;
        }
    }

    /**
     * {@inheritDoc}
     */
    public ComplexityValue getLowerBound() {
        return this.lowerBound;
    }

    /**
     * {@inheritDoc}
     */
    public ComplexityValue getUpperBound() {
        return this.upperBound;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isCompletelyKnown() {
        /* this semantics are correct, but are they good, too? */
        return this.fallbackToYNM().isCompletelyKnown();
    }

    @Override
    public boolean isCompletelyUnknown() {
        return lowerBound.isConstant() && upperBound.isInfinite();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public TruthValue mult(final TruthValue other) {
        final ComplexityYNM cOther = ComplexityYNM.toComplexityYNM(other);
        final ComplexityValue lower = ComplexityValue.constant();
        final ComplexityValue upper = this.upperBound.mult(cOther.upperBound);
        return ComplexityYNM.create(lower, upper);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public TruthValue not() {
        throw new UnsupportedOperationException();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public TruthValue or(final TruthValue other) {
        final ComplexityYNM cOther = ComplexityYNM.toComplexityYNM(other);
        final ComplexityValue lower = this.lowerBound.max(cOther.lowerBound);
        final ComplexityValue upper = this.upperBound.min(cOther.upperBound);
        return ComplexityYNM.create(lower, upper);
    }

    @Override
    public Color toColor() {
        if (upperBound.isFinite() || isCompletelyUnknown()) {
            return this.fallbackToYNM().toColor();
        } else {
            assert !lowerBound.isConstant();
            return Color.BLUE;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return "BOUNDS(" + this.lowerBound + ", " + this.upperBound + ")";
    }

    public String toResultString(Function<ComplexityValue, String> nonPolyLowerBoundConverter, Function<ComplexityValue, String> nonPolyUpperBoundConverter) {
        Export_Util eu = new PLAIN_Util();
        if (this.lowerBound.isConstant() && this.upperBound.isInfinite()) {
            return eu.export("MAYBE");
        }
        String uBound = this.upperBound.export(eu, "O");
        if (this.upperBound.isSuperPolynomial()) {
            uBound = eu.escape(nonPolyUpperBoundConverter.apply(this.upperBound));
        }
        String lBound = this.lowerBound.export(eu, "Omega");
        if (this.lowerBound.isConstant()) {
            lBound = "?";
        } else if (this.lowerBound.isSuperPolynomial()) {
            lBound = eu.escape(nonPolyLowerBoundConverter.apply(this.lowerBound));
        }
        return "WORST_CASE(" + lBound + "," + uBound + ")";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toWstString() {
        return this.toResultString(c -> "NON_POLY", c -> "?");
    }

    @Override
    public String toBenchmarkResult() {
        return toResultString(nonPolyLower -> {
            if (nonPolyLower.isExponential()) return "EXP";
            if (nonPolyLower.isDoubleExponential()) return "2-EXP";
            if (nonPolyLower.isInfinite()) return "INF";
            throw new RuntimeException(nonPolyLower.toString() + " is not a known non-polynomial complexity value!");
        }, nonPolyUpper -> {
            if (nonPolyUpper.isExponential()) return "EXP";
            if (nonPolyUpper.isDoubleExponential()) return "2-EXP";
            if (nonPolyUpper.isInfinite()) return "?";
            throw new RuntimeException(nonPolyUpper.toString() + " is not a known non-polynomial complexity value!");
        });
    }

    @Override
    public boolean isOptimal() {
        return this.lowerBound.equalsAsymptotic(this.upperBound) || this.lowerBound.isSuperPolynomial();
    }

    public ComplexityYNM discardConcreteValues() {
        return ComplexityYNM.create(lowerBound.discardConcreteValue(), upperBound.discardConcreteValue());
    }

}
