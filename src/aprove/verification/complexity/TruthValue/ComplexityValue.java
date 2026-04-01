package aprove.verification.complexity.TruthValue;

import java.math.*;
import java.util.*;
import java.util.function.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.MinMaxExprs.*;
import aprove.verification.oldframework.Logic.*;

public abstract class ComplexityValue implements Exportable, Comparable<ComplexityValue> {

    Optional<MinMaxExpr> concreteValue;

    public Optional<String> exportConcrete(Export_Util eu) {
        return concreteValue.map(x -> x.export(eu));
    }

    public static ComplexityValue constant() {
        return constant(Optional.empty());
    }

    public static ComplexityValue constant(BigInteger concreteValue) {
        return constant(Optional.of(MinMaxExpr.createInt(concreteValue)));
    }

    static ComplexityValue constant(Optional<MinMaxExpr> concreteValue) {
        return new SingletonComplexity(Order.CONSTANT, concreteValue, "1") {
            @Override
            public String export(Export_Util eu, String landauSign) {
                return landauSign + eu.escape("(" + eu.escape("1") + ")");
            }

            @Override
            ComplexityValue withConcreteValue(Optional<MinMaxExpr> concreteValue) {
                return constant(concreteValue);
            }
        };
    }

    public static ComplexityValue polynomial() {
        return polynomial(Optional.empty());
    }

    static ComplexityValue polynomial(Optional<MinMaxExpr> concreteValue) {
        return new SingletonComplexity(Order.POLY, concreteValue) {
            @Override
            public String export(Export_Util eu, String landauSign) {
                return eu.escape(this.toString());
            }

            @Override
            ComplexityValue withConcreteValue(Optional<MinMaxExpr> concreteValue) {
                return polynomial(concreteValue);
            }
        };
    }

    public static ComplexityValue exponential() {
        return exponential(Optional.empty());
    }

    static ComplexityValue exponential(Optional<MinMaxExpr> concreteValue) {
        return new SingletonComplexity(Order.EXPONENTIAL, concreteValue, "EXP"){
            @Override
            public String export(Export_Util eu, String landauSign) {
                return eu.escape(this.toString());
            }

            @Override
            ComplexityValue withConcreteValue(Optional<MinMaxExpr> concreteValue) {
                return exponential(concreteValue);
            }
        };
    }

    public static ComplexityValue doubleExponential() {
        return doubleExponential(Optional.empty());
    }
    
    static ComplexityValue doubleExponential(Optional<MinMaxExpr> concreteValue) {
        return new SingletonComplexity(Order.DOUBLEEXPONENTIAL, concreteValue, "2-EXP"){
            @Override
            public String export(Export_Util eu, String landauSign) {
                return eu.escape(this.toString());
            }

            @Override
            ComplexityValue withConcreteValue(Optional<MinMaxExpr> concreteValue) {
                return doubleExponential(concreteValue);
            }
        };
    }

    public static ComplexityValue finite() {
        return finite(Optional.empty());
    }

    static final ComplexityValue finite(Optional<MinMaxExpr> concreteValue) {
        return new SingletonComplexity(Order.FINITE, concreteValue) {
            @Override
            public String export(Export_Util eu, String landauSign) {
                return eu.escape(this.toString());
            }

            @Override
            ComplexityValue withConcreteValue(Optional<MinMaxExpr> concreteValue) {
                return finite(concreteValue);
            }
        };
    }

    public static ComplexityValue infinite() {
        return INF;
    }

    static final ComplexityValue INF =
        new SingletonComplexity(Order.INFINITE, Optional.empty(), "INF") {
            @Override
            public String export(Export_Util eu, String landauSign) {
                return eu.escape(this.toString());
            }

            @Override
            ComplexityValue withConcreteValue(Optional<MinMaxExpr> concreteVale) {
                return INF;
            }
    };

    public static ComplexityValue fixedDegreePoly(int n) {
        return fixedDegreePoly(n, Optional.empty());
    }

    private static ComplexityValue fixedDegreePoly(final int n, Optional<MinMaxExpr> concreteValue) {
        return n == 0 ? constant(concreteValue) : new FixedDegreePoly(n, concreteValue);
    }

    public static ComplexityValue linear() {
        return linear(Optional.empty());
    }

    private static ComplexityValue linear(Optional<MinMaxExpr> concreteValue) {
        return fixedDegreePoly(1, concreteValue);
    }

    public static ComplexityValue quadratic() {
        return quadratic(Optional.empty());
    }

    private static ComplexityValue quadratic(Optional<MinMaxExpr> concreteValue) {
        return fixedDegreePoly(2, concreteValue);
    }

    /**
     * Total ordering of the different ComplexityYNM types.
     *
     * Each ComplexityYNM implementation
     *
     * The order of Order is important.
     */
    protected enum Order {
        CONSTANT(YNM.YES),
        FIXED_DEGREE_POLY(YNM.YES),
        POLY(YNM.YES),
        FIXED_BASE_EXPONENTIAL_FUNCTION(YNM.YES),
        EXPONENTIAL(YNM.YES), // Make this more detailed?
        DOUBLEEXPONENTIAL(YNM.YES),
        FINITE(YNM.YES),
        UNKNOWN(YNM.MAYBE),
        INFINITE(YNM.NO);

        final YNM fallback;
        private Order(final YNM fallback) {
            this.fallback = fallback;
        }

    }

    final Order order;

    protected ComplexityValue(final Order order, Optional<MinMaxExpr> concreteValue) {
        this.order = order;
        this.concreteValue = concreteValue;
    }

    private ComplexityValue max(final ComplexityValue other, Optional<MinMaxExpr> newConcreteValue) {
        final int thisOrd = this.order.ordinal();
        final int otherOrd = other.order.ordinal();
        if (thisOrd > otherOrd) {
            return this.withConcreteValue(newConcreteValue);
        } else if (thisOrd == otherOrd) {
            if (this.innerCompareTo(other) >= 0) {
                return this.withConcreteValue(newConcreteValue);
            } else {
                return other.withConcreteValue(newConcreteValue);
            }
        } else {
            return other.withConcreteValue(newConcreteValue);
        }
    }

    public ComplexityValue approximateMax(final ComplexityValue other) {
        return max(other, approximateMax(other.concreteValue));
    }

    public ComplexityValue max(final ComplexityValue other) {
        return max(other, maxConcreteValue(other.concreteValue));
    }

    private ComplexityValue min(ComplexityValue other, Optional<MinMaxExpr> newConcreteValue) {
        final int thisOrd = this.order.ordinal();
        final int otherOrd = other.order.ordinal();
        if (thisOrd < otherOrd) {
            return this.withConcreteValue(newConcreteValue);
        } else if (thisOrd == otherOrd) {
            if (this.innerCompareTo(other) <= 0) {
                return this.withConcreteValue(newConcreteValue);
            } else {
                return other.withConcreteValue(newConcreteValue);
            }
        } else {
            return other.withConcreteValue(newConcreteValue);
        }
    }

    public ComplexityValue approximateMin(final ComplexityValue other) {
        return min(other, approximateMin(other.concreteValue));
    }

    public ComplexityValue min(final ComplexityValue other) {
        return min(other, min(other.concreteValue));
    }

    @Override
    public int compareTo(final ComplexityValue other) {
        if (this == other) return 0;
        int c = this.order.compareTo(other.order);
        if (c != 0) return c;
        return this.innerCompareTo(other);
    }

    /**
     * Compares this with a ComplexityValue of the same type.
     */
    protected int innerCompareTo(ComplexityValue other) {
        if (this.concreteValue.isPresent() && other.concreteValue.isPresent()) {
            return this.concreteValue.get().compareTo(other.concreteValue.get());
        } else {
            return 0;
        }
    }

    public abstract YNM fallbackToYNM();

    public ComplexityValue mult(final ComplexityValue other) {
        switch (this.order) {
            case CONSTANT:
                return other.withConcreteValue(multiplyConcreteValue(concreteValue));
            case FIXED_DEGREE_POLY:
                switch (other.order) {
                    case CONSTANT:
                        return this.withConcreteValue(multiplyConcreteValue(other.concreteValue));
                    case FIXED_DEGREE_POLY:
                        if (this instanceof FixedDegreePoly && other instanceof FixedDegreePoly) {
                            return ((FixedDegreePoly)this).multiply((FixedDegreePoly)other);
                        } else {
                            throw new RuntimeException();
                        }
                } // fall through
        } // fall through
        return this.max(other).withConcreteValue(multiplyConcreteValue(other.concreteValue));
    }

    public ComplexityValue discardConcreteValue() {
        return this.withConcreteValue(Optional.empty());
    }

    public ComplexityValue withConcreteValue(MinMaxExpr concreteValue) {
        return this.withConcreteValue(Optional.of(concreteValue));
    }

    abstract ComplexityValue withConcreteValue(Optional<MinMaxExpr> concreteValue);

    private Optional<MinMaxExpr> combineConcreteValue(Optional<MinMaxExpr> o, BinaryOperator<MinMaxExpr> combinator) {
        Optional<MinMaxExpr> newConcreteValue;
        if (concreteValue.isPresent() && o.isPresent()) {
            newConcreteValue = Optional.of(combinator.apply(concreteValue.get(), o.get()).normalize());
        } else {
            newConcreteValue = Optional.empty();
        }
        return newConcreteValue;
    }

    public boolean isConstant() {
        return this.order == Order.CONSTANT;
    }

    public boolean isPoly(int degree) {
        return false;
    }

    public boolean isInfinite() {
        return this.order == Order.INFINITE;
    }

    public boolean isExponential() {
        return this.order == Order.EXPONENTIAL;
    }

    public boolean isDoubleExponential() {
        return this.order == Order.DOUBLEEXPONENTIAL;
    }

    public boolean isSuperPolynomial() {
        return this.order.compareTo(Order.POLY) > 0;
    }

    public Optional<MinMaxExpr> multiplyConcreteValue(Optional<MinMaxExpr> o) {
        return combineConcreteValue(o, MinMaxExpr::createTimes);
    }

    public Optional<MinMaxExpr> approximateMax(Optional<MinMaxExpr> o) {
        Optional<MinMaxExpr> newConcreteValue;
        if (concreteValue.isPresent() && o.isPresent()) {
            if (concreteValue.get().equals(o.get())) {
                newConcreteValue = concreteValue;
            } else {
                int comp = concreteValue.get().compareTo(o.get());
                if (comp < 0) {
                    newConcreteValue = o;
                } else if (comp > 0) {
                    newConcreteValue = concreteValue;
                } else {
                    newConcreteValue = Optional.of(MinMaxExpr.createMax(concreteValue.get(), o.get()).normalize());
                }
            }
        } else if (concreteValue.isPresent()) {
            newConcreteValue = concreteValue;
        } else if (o.isPresent()) {
            newConcreteValue = o;
        } else {
            newConcreteValue = Optional.empty();
        }
        return newConcreteValue;
    }

    public Optional<MinMaxExpr> maxConcreteValue(Optional<MinMaxExpr> o) {
        return combineConcreteValue(o, MinMaxExpr::createMax);
    }

    public Optional<MinMaxExpr> approximateMin(Optional<MinMaxExpr> o) {
        Optional<MinMaxExpr> newConcreteValue;
        if (concreteValue.isPresent() && o.isPresent()) {
            if (concreteValue.get().equals(o.get())) {
                newConcreteValue = concreteValue;
            } else {
                int comp = concreteValue.get().compareTo(o.get());
                if (comp < 0) {
                    newConcreteValue = concreteValue;
                } else if (comp > 0) {
                    newConcreteValue = o;
                } else {
                    newConcreteValue = Optional.of(MinMaxExpr.createMin(concreteValue.get(), o.get()).normalize());
                }
            }
        } else if (concreteValue.isPresent()) {
            newConcreteValue = concreteValue;
        } else if (o.isPresent()) {
            newConcreteValue = o;
        } else {
            newConcreteValue = Optional.empty();
        }
        return newConcreteValue;
    }

    public Optional<MinMaxExpr> min(Optional<MinMaxExpr> o) {
        Optional<MinMaxExpr> newConcreteValue;
        if (concreteValue.isPresent() && o.isPresent()) {
            newConcreteValue = Optional.of(MinMaxExpr.createMin(concreteValue.get(), o.get()).normalize());
        } else if (concreteValue.isPresent()) {
            newConcreteValue = concreteValue;
        } else if (o.isPresent()) {
            newConcreteValue = o;
        } else {
            newConcreteValue = Optional.empty();
        }
        return newConcreteValue;
    }

    public Optional<MinMaxExpr> addConcreteValue(Optional<MinMaxExpr> o) {
        return combineConcreteValue(o, MinMaxExpr::createPlus);
    }

    public abstract String export(Export_Util eu, String landauSign);

    @Override
    public String toString() {
        PLAIN_Util eu = new PLAIN_Util();
        return exportConcrete(eu).orElse(export(eu));
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + concreteValue.hashCode();
        result = prime * result + ((order == null) ? 0 : order.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        ComplexityValue other = (ComplexityValue) obj;
        if (!concreteValue.equals(other.concreteValue))
            return false;
        if (order != other.order)
            return false;
        return true;
    }

    public boolean equalsAsymptotic(ComplexityValue other) {
        return this.discardConcreteValue().equals(other.discardConcreteValue());
    }

    public Optional<MinMaxExpr> getConcreteValue() {
        return concreteValue;
    }

    public ComplexityValue add(ComplexityValue other) {
        return this.max(other).withConcreteValue(addConcreteValue(other.concreteValue));
    }

    public boolean isFinite() {
        return !isInfinite();
    }

}
