package aprove.verification.complexity.CpxIntTrsProblem.Structures;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Macros.*;
import immutables.*;

public abstract class LocalComplexityValue implements Immutable, Comparable<LocalComplexityValue>, Exportable {

    private static final SMTExpression<SInt> large_constant = Ints.constant(new BigInteger(
        "1000000000000000000000000000000000"));

    public static final class AddBound extends LocalComplexityValue {
        private AddBound() {
        }

        @Override
        public String export(Export_Util eu) {
            if (eu instanceof HTML_Util) {
                return "+&#773;";
            }
            return "+_";
        }

        @Override
        protected int getCardinality() {
            return 3;
        }

        @Override
        public ComplexityValue getComplexityValue() {
            return ComplexityValue.linear();
        }

        @Override
        public SMTExpression<SInt> createSMTExpression(List<SMTExpression<SInt>> abs_vars) {
            return Ints.add(LocalComplexityValue.large_constant, Ints.add(abs_vars));
        }

    }

    public static final class AddConstantBound extends LocalComplexityValue {
        private AddConstantBound() {
        }

        @Override
        public String export(Export_Util eu) {
            if (eu instanceof HTML_Util) {
                return "+&#775;";
            }
            return "+.";
        }

        @Override
        protected int getCardinality() {
            return 2;
        }

        @Override
        public ComplexityValue getComplexityValue() {
            return ComplexityValue.linear();
        }

        @Override
        public SMTExpression<SInt> createSMTExpression(List<SMTExpression<SInt>> abs_vars) {
            return Ints.add(LocalComplexityValue.large_constant, IntMaxMacro.call(abs_vars));
        }
    }

    public static final class EqualityBound extends LocalComplexityValue {
        private EqualityBound() {
        }

        @Override
        public String export(Export_Util eu) {
            if (eu instanceof HTML_Util) {
                return "=&#775;";
            }
            return "=.";
        }

        @Override
        protected int getCardinality() {
            return 1;
        }

        @Override
        public ComplexityValue getComplexityValue() {
            return ComplexityValue.linear();
        }

        @Override
        public SMTExpression<SInt> createSMTExpression(List<SMTExpression<SInt>> abs_vars) {
            return IntMaxMacro.call(LocalComplexityValue.large_constant, IntMaxMacro.call(abs_vars));
        }

    }

    public static final class PolynomialBound extends LocalComplexityValue {
        private final int degree;

        private PolynomialBound(int degree) {
            // Integer.MAX_VALUE - 100 because we need space (in the cardinality) for special values between P_0 and P_1
            if (degree < 0 || degree > Integer.MAX_VALUE - 100) {
                throw new IllegalArgumentException("invalid degree");
            }
            this.degree = degree;
        }

        @Override
        public String export(Export_Util eu) {
            if (eu instanceof HTML_Util) {
                return "P" + eu.sub(Integer.toString(this.degree));
            }
            return "P_" + this.degree;
        }

        @Override
        protected int getCardinality() {
            if (this.degree == 0) {
                return this.degree;
            }
            return this.degree + 3; // to make space for special values
        }

        @Override
        public ComplexityValue getComplexityValue() {
            if (this.degree == 0) {
                return ComplexityValue.constant();
            }
            return ComplexityValue.fixedDegreePoly(this.degree);
        }

        @Override
        public Integer getDegree() {
            return this.degree;
        }

        @Override
        public SMTExpression<SInt> createSMTExpression(List<SMTExpression<SInt>> abs_vars) {
            switch (this.degree) {
            case 0:
                assert abs_vars.size() == 0;
                return LocalComplexityValue.large_constant;
            case 1:
                return Ints.add(LocalComplexityValue.large_constant, Ints.times(LocalComplexityValue.large_constant, Ints.add(abs_vars)));
            default:
                throw new RuntimeException("not implemented");
            }
        }
    }

    public static final class Unbounded extends LocalComplexityValue {
        private Unbounded() {
        }

        @Override
        public String export(Export_Util eu) {
            return eu.bold("?");
        }

        @Override
        protected int getCardinality() {
            return Integer.MAX_VALUE;
        }

        @Override
        public ComplexityValue getComplexityValue() {
            return ComplexityValue.infinite();
        }

        @Override
        public SMTExpression<SInt> createSMTExpression(List<SMTExpression<SInt>> abs_vars) {
            throw new RuntimeException("not implemented");
        }
    }

    private static final PolynomialBound[] cache = new PolynomialBound[16];

    static {
        for (int i = 0, l = LocalComplexityValue.cache.length; i < l; ++i) {
            LocalComplexityValue.cache[i] = new PolynomialBound(i + 1);
        }
    }

    public static final Unbounded UNBOUNDED = new Unbounded();
    public static final AddConstantBound ADDCONSTANTBOUND = new AddConstantBound();
    public static final AddBound ADDBOUND = new AddBound();
    public static final EqualityBound EQUALITYBOUND = new EqualityBound();
    public static final LocalComplexityValue POL0 = LocalComplexityValue.createPolBound(0);
    public static final LocalComplexityValue POL1 = LocalComplexityValue.createPolBound(1);

    public static PolynomialBound createPolBound(int degree) {
        if (0 < degree && degree <= LocalComplexityValue.cache.length) {
            return LocalComplexityValue.cache[degree - 1];
        }
        return new PolynomialBound(degree);
    }

    private static LocalComplexityValue fromCardinality(int i) {
        switch (i) {
        case 0:
            return LocalComplexityValue.POL0;
        case 1:
            return LocalComplexityValue.EQUALITYBOUND;
        case 2:
            return LocalComplexityValue.ADDCONSTANTBOUND;
        case 3:
            return LocalComplexityValue.ADDBOUND;
        default:
            return LocalComplexityValue.createPolBound(i - 3);
        }
    }

    /*
     * testing output...
    public static void main(String[] args) {
        LocalComplexityValue[] cs = {POL0, EQUALITYBOUND, ADDCONSTANTBOUND, ADDBOUND, createPolBound(3), UNBOUNDED };

        for (LocalComplexityValue c1 : cs) {
            for (LocalComplexityValue c2 : cs) {
                System.out.print(c1.multiply(c2) + "\t");
            }
            System.out.println();
        }
    }
    */

    /*
     * This class should not be inherited outside of this file.
     */
    private LocalComplexityValue() {
    }

    @Override
    public int compareTo(LocalComplexityValue o) {
        return this.getCardinality() - o.getCardinality();
    }

    /**
     * Compute the {@code c}-fold composition of {@code this}.
     * @param c
     * @return
     */
    public LocalComplexityValue composition(LocalComplexityValue c) {
        LocalComplexityValue b = this;
        if (b.getDegree() == 0 || b instanceof EqualityBound) {
            return b;
        }
        if (b instanceof AddConstantBound) {
            return c;
        }
        return LocalComplexityValue.UNBOUNDED;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null || !(obj instanceof LocalComplexityValue)) {
            return false;
        }
        LocalComplexityValue o = (LocalComplexityValue) obj;
        return this.getCardinality() == o.getCardinality();
    }

    // map values to natural numbers
    protected abstract int getCardinality();

    public abstract ComplexityValue getComplexityValue();

    public Integer getDegree() {
        return null;
    }

    @Override
    public int hashCode() {
        return this.getCardinality();
    }

    private static int[][] multiplyCardinalityTable = { {0, 0, 0, 0 }, {0, 1, 2, 2 }, {0, 2, 2, 4 }, {0, 3, 3, 4 } };

    /**
     * Multiplication of complexities.
     * @param other
     * @return
     */
    public LocalComplexityValue multiply(LocalComplexityValue other) {
        int c1 = this.getCardinality();
        int c2 = other.getCardinality();

        if (c2 == 0) {
            return LocalComplexityValue.POL0;
        }

        if (c1 < 4 && c2 < 4) {
            return LocalComplexityValue.fromCardinality(LocalComplexityValue.multiplyCardinalityTable[c1][c2]);
        }

        if (c1 == Integer.MAX_VALUE || c2 == Integer.MAX_VALUE) {
            return LocalComplexityValue.UNBOUNDED;
        }

        int deg1 = this.getDegree() == null ? 1 : this.getDegree();
        int deg2 = other.getDegree() == null ? 1 : other.getDegree();

        return LocalComplexityValue.createPolBound(deg1 * deg2);
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public LocalComplexityValue max(LocalComplexityValue other) {
        if (this.compareTo(other) >= 0) {
            return this;
        }
        return other;
    }

    public abstract SMTExpression<SInt> createSMTExpression(List<SMTExpression<SInt>> abs_vars);

    public static LocalComplexityValue fromComplexityValue(ComplexityValue c) {
        if (c.isConstant()) {
            return POL0;
        }
        if (c instanceof FixedDegreePoly) {
            FixedDegreePoly cf = (FixedDegreePoly) c;
            return LocalComplexityValue.createPolBound(cf.getDegree());
        }
        return LocalComplexityValue.UNBOUNDED;
    }
}
