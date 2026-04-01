package aprove.verification.complexity.LowerBounds.BasicStructures;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.Complexity.*;
import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;
import aprove.verification.complexity.LowerBounds.Util.Transformations.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;

public class Lemma extends AbstractRule {

    private Complexity complexity;

    private Lemma(TRSFunctionApplication lhs, TRSTerm rhs, Complexity complexity) {
        super(lhs, rhs);
        this.complexity = complexity;
    }

    public Lemma(Conjecture conjecture, Complexity complexity) {
        this(conjecture.getLeft(), conjecture.getRight(), complexity);
    }

    @Override
    public String export(Export_Util eu) {
        String res = super.export(eu);
        res += eu.escape(", rt ");
        res += eu.isElement();
        res += eu.appSpace();
        res += eu.Omega();
        res += eu.escape("(");
        res += this.complexity.export(eu);
        res += eu.escape(")");
        return res;
    }

    @Override
    public Complexity getComplexity() {
        return this.complexity;
    }

    public int getDegreeOfStartTermSize(TrsTypes types) {
        return new TermToSumOfPolynomials(types).transform(this.getLeft()).getDegree();
    }


    @Override
    public Lemma normalizeVariables() {
        Map<TRSVariable, TRSVariable> renaming = new LinkedHashMap<>();
        ImmutablePair<? extends TRSTerm, Integer> p = this.getLeft().renumberVariables(renaming, "x", 0);
        TRSFunctionApplication newLhs = (TRSFunctionApplication) p.x;
        int count = p.y;
        p = this.getRight().renumberVariables(renaming, "x", count);
        TRSTerm newRhs = p.x;
        Complexity newComplexity = this.complexity.replaceVariables(renaming);
        return new Lemma(newLhs, newRhs, newComplexity);
    }

    @Override
    Lemma cloneWith(TRSFunctionApplication newLhs, TRSTerm newRhs) {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getIndex() {
        return "L";
    }

    @Override
    public AbstractRule renameVariables(RenamingCentral renamingCentral) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Lemma applySubstitution(TRSSubstitution sigma, TrsTypes types) {
        Complexity newComplexity = this.applySubstitutionToComplexity(sigma, types);
        return new Lemma(this.lhs.applySubstitution(sigma),
                this.rhs.applySubstitution(sigma),
                newComplexity);
    }

    private Complexity applySubstitutionToComplexity(TRSSubstitution sigma, TrsTypes types) {
        Complexity complexity = this.getComplexity();
        Complexity newComplexity;
        if (complexity.isPolynomial()) {
            newComplexity = ((PolynomialComplexity) complexity).applySubstitution(sigma, types);
        } else {
            newComplexity = complexity;
        }
        return newComplexity;
    }

    public ComplexityValue getIrc(TrsTypes types) {
        Complexity complexity = this.getComplexity();
        if (complexity.isPolynomial()) {
            int degree = ((PolynomialComplexity) complexity).getDegree();
            if (degree == 0) {
                return ComplexityValue.constant();
            } else {
                return ComplexityValue.fixedDegreePoly(degree / getDegreeOfStartTermSize(types));
            }
        } else {
            return complexity.asymptotic();
        }
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + ((this.complexity == null) ? 0 : this.complexity.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (!super.equals(obj)) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        Lemma other = (Lemma) obj;
        if (this.complexity == null) {
            if (other.complexity != null) {
                return false;
            }
        } else if (!this.complexity.equals(other.complexity)) {
            return false;
        }
        return true;
    }

    public void addToTrs(LowerBoundsTrs trs) {
        trs.add(this);
    }

    public boolean isIndefinite(LowerBoundsToolbox toolbox) {
        return this.rhs.equals(toolbox.arbitraryTerm);
    }
}
