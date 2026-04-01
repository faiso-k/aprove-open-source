package aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem;

import java.math.*;
import java.util.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;


/** Here we store all information related to the sampling points we generated. */
public abstract class SampleConjectureMap implements Iterable<RewriteSequence> {

    // the rewrite sequence (value) loops the rule we are interested in 'key' times
    private Map<BigInteger, RewriteSequence> samplingPoints = new LinkedHashMap<>();
    // we have as many coefficients as sampling points
    private List<NamedSymbol0<SInt>> coefficients = new ArrayList<>();
    // A term that matches the normal forms of all sequences used as sampling points.
    private TRSTerm scheme;
    private Set<AbstractRule> rules = new LinkedHashSet<>();
    private Set<Position> rhsVariables;


    public SampleConjectureMap(TRSTerm scheme, Set<AbstractRule> rules, Set<Position> rhsVariables) {
        this.scheme = scheme;
        for (AbstractRule rule: rules) {
            this.rules.add(rule.normalizeVariables());
        }
        this.rhsVariables = rhsVariables;
    }

    public boolean add(RewriteSequence sampleConjecture) {
        BigInteger index = this.getIndex(sampleConjecture);
        if (index == null) {
            return false;
        }
        int nextCoefficient = this.coefficients.size();
        if (!this.samplingPoints.containsKey(index)) {
            this.coefficients.add(new NamedSymbol0<SInt>(SInt.representative, "c" + nextCoefficient));
        }
        this.samplingPoints.put(index, sampleConjecture);
        return true;
    }

    abstract BigInteger getIndex(RewriteSequence conjecture);

    public Set<BigInteger> availableSamplingPoints() {
        return this.samplingPoints.keySet();
    }

    public RewriteSequence getSampleConjectureFor(BigInteger recursionDepth) {
        return this.samplingPoints.get(recursionDepth);
    }

    public int size() {
        return this.samplingPoints.size();
    }

    public TRSTerm getScheme() {
        return this.scheme;
    }

    public List<NamedSymbol0<SInt>> getCoefficients() {
        return this.coefficients;
    }

    public boolean matches(TRSTerm term) {
        return this.scheme.matches(term);
    }

    public boolean schemeEquals(TRSTerm t) {
        return this.scheme.matches(t) && t.matches(this.scheme);
    }

    public SMTExpression<SInt> getCoefficient(int i) {
        return this.coefficients.get(i);
    }

    public boolean rhsVariablesEquals(Set<Position> rhsVariables) {
        return this.rhsVariables.equals(rhsVariables);
    }

    public boolean isEmpty() {
        return this.samplingPoints.isEmpty();
    }

    @Override
    public Iterator<RewriteSequence> iterator() {
        return this.samplingPoints.values().iterator();
    }

    public boolean rulesEqual(Set<AbstractRule> rules) {
        Set<AbstractRule> normalized = new LinkedHashSet<>();
        for (AbstractRule r: rules) {
            normalized.add(r.normalizeVariables());
        }
        return this.rules.equals(normalized);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.rhsVariables == null) ? 0 : this.rhsVariables.hashCode());
        result = prime * result + ((this.rules == null) ? 0 : this.rules.hashCode());
        result = prime * result + ((this.scheme == null) ? 0 : this.scheme.hashCode());
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
        SampleConjectureMap other = (SampleConjectureMap) obj;
        if (this.rhsVariables == null) {
            if (other.rhsVariables != null) {
                return false;
            }
        } else if (!this.rhsVariables.equals(other.rhsVariables)) {
            return false;
        }
        if (this.rules == null) {
            if (other.rules != null) {
                return false;
            }
        } else if (!this.rules.equals(other.rules)) {
            return false;
        }
        if (this.scheme == null) {
            if (other.scheme != null) {
                return false;
            }
        } else if (!this.scheme.equals(other.scheme)) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        String res = "scheme: " + this.scheme;
        res += ", rules: " + this.rules;
        res += ", rhs-vars: " + this.rhsVariables;
        return res;
    }

}
