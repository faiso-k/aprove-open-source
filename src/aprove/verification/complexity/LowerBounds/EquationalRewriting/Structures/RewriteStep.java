package aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.Complexity.*;
import aprove.verification.complexity.LowerBounds.Util.Transformations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

public class RewriteStep {

    private AbstractRule rule;
    private TRSTerm oldTerm;
    private TRSSubstitution sigma;
    private Position pi;

    public RewriteStep(AbstractRule rule, TRSTerm term, Position pi, TRSSubstitution sigma) {
        this.rule = rule;
        this.oldTerm = term;
        this.sigma = sigma;
        this.pi = pi;
    }

    public Complexity getComplexity(LowerBoundsToolbox toolbox) {
        assert !this.rule.getComplexity().isExponential(): "Analysis should terminate when we proved EXP!";
        if (!this.rule.getComplexity().isPolynomial()) {
            return this.rule.getComplexity();
        }
        PolynomialComplexity complexity = (PolynomialComplexity) this.rule.getComplexity();
        PolynomialComplexity res = complexity;
        for (String varName : complexity.getVariables()) {
            TRSVariable var = TRSTerm.createVariable(varName);
            TRSTerm t = this.sigma.substitute(var);
            SimplePolynomial termSize = new TermToPolynomial(toolbox.types).transform(t);
            res = res.substitute(varName, termSize);
        }
        return res;
    }

    public AbstractRule getRule() {
        return this.rule;
    }

    public TRSSubstitution getSigma() {
        return this.sigma;
    }

    public Position getPi() {
        return this.pi;
    }

    public RewriteStep replaceAll(Map<TRSTerm, TRSTerm> map) {
        TRSTerm newTerm = this.oldTerm.replaceAll(map);
        TRSSubstitution newSigma = TRSSubstitution.EMPTY_SUBSTITUTION;
        for (Entry<TRSVariable, ? extends TRSTerm> e: this.sigma.toMap().entrySet()) {
            newSigma = newSigma.extend(TRSSubstitution.create(
                    e.getKey(),
                    e.getValue().replaceAll(map)));
        }
        return new RewriteStep(this.rule, newTerm, this.pi, newSigma);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.pi == null) ? 0 : this.pi.hashCode());
        result = prime * result + ((this.rule == null) ? 0 : this.rule.hashCode());
        result = prime * result + ((this.sigma == null) ? 0 : this.sigma.hashCode());
        result = prime * result + ((this.oldTerm == null) ? 0 : this.oldTerm.hashCode());
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
        RewriteStep other = (RewriteStep) obj;
        if (this.pi == null) {
            if (other.pi != null) {
                return false;
            }
        } else if (!this.pi.equals(other.pi)) {
            return false;
        }
        if (this.rule == null) {
            if (other.rule != null) {
                return false;
            }
        } else if (!this.rule.equals(other.rule)) {
            return false;
        }
        if (this.sigma == null) {
            if (other.sigma != null) {
                return false;
            }
        } else if (!this.sigma.equals(other.sigma)) {
            return false;
        }
        if (this.oldTerm == null) {
            if (other.oldTerm != null) {
                return false;
            }
        } else if (!this.oldTerm.equals(other.oldTerm)) {
            return false;
        }
        return true;
    }

    public TRSTerm getResult() {
        return this.oldTerm.replaceAt(this.pi, this.rule.getRight()).applySubstitution(this.sigma);
    }

    @Override
    public String toString() {
        return this.oldTerm.toString() + " -" + this.sigma.restrictTo(this.oldTerm.getVariables()) + "-> " + this.getResult();
    }

    public TRSTerm getOldTerm() {
        return this.oldTerm;
    }

}
