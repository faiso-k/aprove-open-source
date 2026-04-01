package aprove.verification.complexity.LowerBounds.BasicStructures;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.complexity.LowerBounds.Util.Transformations.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

public abstract class Complexity implements Comparable<Complexity>, Exportable {

    public static final PolynomialComplexity ZERO = new PolynomialComplexity(SimplePolynomial.ZERO);
    public static final PolynomialComplexity ONE = new PolynomialComplexity(SimplePolynomial.ONE);

    public static PolynomialComplexity linear(String var) {
        return new PolynomialComplexity(SimplePolynomial.create(var));
    }

    public abstract boolean isConstant();

    public abstract boolean isPolynomial();

    public abstract boolean isExponential();

    public abstract boolean isUnknown();

    public abstract ComplexityValue asymptotic();

    public static class PolynomialComplexity extends Complexity {

        private SimplePolynomial polynomial;

        public PolynomialComplexity(SimplePolynomial polynomial) {
            this.polynomial = polynomial;
        }

        @Override
        public boolean isConstant() {
            return this.polynomial.isConstant();
        }

        @Override
        public boolean isPolynomial() {
            return true;
        }

        @Override
        public boolean isExponential() {
            return false;
        }

        @Override
        public boolean isUnknown() {
            return false;
        }

        public Set<String> getVariables() {
            return this.polynomial.getIndefinites();
        }

        public PolynomialComplexity substitute(String varName, SimplePolynomial value) {
            return new PolynomialComplexity(this.polynomial.substitute(Collections.singletonMap(varName, value)));
        }

        public Complexity applySubstitution(TRSSubstitution sigma, TrsTypes types) {
            Map<TRSVariable, ? extends TRSTerm> origMap = sigma.toMap();
            Map<String, SimplePolynomial> newMap = new LinkedHashMap<>();
            for (Entry<TRSVariable, ? extends TRSTerm> e : origMap.entrySet()) {
                TRSVariable var = e.getKey();
                SimplePolynomial replacement = new TermToPolynomial(types).transform(e.getValue());
                newMap.put(var.getName(), replacement);
            }
            return new PolynomialComplexity(this.polynomial.substitute(newMap));
        }

        @Override
        public int compareTo(Complexity that) {
            if (that.isPolynomial()) {
                return this.asymptotic().compareTo(that.asymptotic());
            } else {
                return -that.compareTo(this);
            }
        }

        public PolynomialComplexity max(PolynomialComplexity that) {
            if (this.polynomial.getDegree() > that.polynomial.getDegree()) {
                return this;
            } else if (this.polynomial.getDegree() < that.polynomial.getDegree()) {
                return that;
            } else if (this.polynomial.compareTo(that.polynomial) >= 0) {
                return this;
            } else {
                return that;
            }
        }

        public PolynomialComplexity times(PolynomialComplexity that) {
            return new PolynomialComplexity(this.polynomial.times(that.polynomial));
        }

        public PolynomialComplexity plus(PolynomialComplexity that) {
            return new PolynomialComplexity(this.polynomial.plus(that.polynomial));
        }

        public int getDegree() {
            if (this.polynomial.isConstant()) {
                return 0;
            } else {
                return this.polynomial.getDegree();
            }
        }

        @Override
        public ComplexityValue asymptotic() {
            if (polynomial.isConstant()) {
                return ComplexityValue.constant();
            } else {
                return ComplexityValue.fixedDegreePoly(polynomial.getDegree());
            }
        }

        @Override
        public String toString() {
            return this.asymptotic().toString();
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((this.polynomial == null) ? 0 : this.polynomial.hashCode());
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
            PolynomialComplexity other = (PolynomialComplexity) obj;
            if (this.polynomial == null) {
                if (other.polynomial != null) {
                    return false;
                }
            } else if (!this.polynomial.equals(other.polynomial)) {
                return false;
            }
            return true;
        }

        @Override
        public String export(Export_Util eu) {
            return this.polynomial.export(eu);
        }

        public PolynomialComplexity setCoefficientsToOne() {
            Map<IndefinitePart, BigInteger> newMonomials = new LinkedHashMap<>();
            for (Entry<IndefinitePart, BigInteger> e : this.polynomial.getSimpleMonomials().entrySet()) {
                newMonomials.put(e.getKey(), BigInteger.ONE);
            }
            return new PolynomialComplexity(SimplePolynomial.create(newMonomials));
        }

        @Override
        public Complexity replaceVariables(Map<TRSVariable, TRSVariable> renaming) {
            Map<String, String> polyRenaming = new LinkedHashMap<>();
            for (Entry<TRSVariable, TRSVariable> e: renaming.entrySet()) {
                polyRenaming.put(e.getKey().getName(), e.getValue().getName());
            }
            return new PolynomialComplexity(polynomial.replace(polyRenaming));
        }

    }

    public static Complexity EXPONENTIAL = new Complexity() {

        @Override
        public boolean isConstant() {
            return false;
        }

        @Override
        public boolean isPolynomial() {
            return false;
        }

        @Override
        public boolean isExponential() {
            return true;
        }

        @Override
        public boolean isUnknown() {
            return false;
        }

        @Override
        public int compareTo(Complexity that) {
            if (that == this) {
                return 0;
            } else if (that.isExponential()) {
                return -1;
            } else {
                return 1;
            }
        }

        @Override
        public ComplexityValue asymptotic() {
            return ComplexityValue.exponential();
        }

        @Override
        public String toString() {
            return "Exponential";
        }

        @Override
        public String export(Export_Util eu) {
            return eu.escape("EXP");
        }

    };

    public static Complexity UNKNOWN = new Complexity() {

        @Override
        public boolean isConstant() {
            return false;
        }

        @Override
        public boolean isPolynomial() {
            return false;
        }

        @Override
        public boolean isExponential() {
            return false;
        }

        @Override
        public boolean isUnknown() {
            return true;
        }

        @Override
        public int compareTo(Complexity that) {
            if (that.isUnknown()) {
                return 0;
            } else {
                return -1;
            }
        }

        @Override
        public ComplexityValue asymptotic() {
            throw new UnsupportedOperationException();
        }

        @Override
        public String toString() {
            return "Unknown Complexity";
        }

        @Override
        public String export(Export_Util eu) {
            return eu.export("unknown complexity");
        }
    };

    @SuppressWarnings("unused")
    public Complexity replaceVariables(Map<TRSVariable, TRSVariable> renaming) {
        return this;
    }

}
