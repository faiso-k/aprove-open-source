package aprove.verification.dpframework.DPProblem.TheoremProver;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * A type assumption encapsulates the assumed type of constructors, variables
 * and defined functions
 *
 * @author micpar
 * @version $Id$
 */

public class TypeAssumption {

    /*
     * attributes
     */
    private Map<String, Signature> typeAssumption = null;

    /**
     * Creates empty type assumption.
     */
    public TypeAssumption() {
        this.typeAssumption = new LinkedHashMap<String, Signature>();
    }

    /**
     * Copy constructor for type assumption
     *
     * @param typeAssumption
     */
    public TypeAssumption(Map<String, Signature> typeAssumption) {
        this.typeAssumption = typeAssumption;
    }

    /**
     * @param f
     * @param s
     * @return true if signature was successfully added (see {@link Signature})
     */
    public boolean addSignatureForSymbol(String f, Signature s) {
        if (this.typeAssumption.containsKey(f)) {
            return false;
        }
        this.typeAssumption.put(f, s);
        return true;
    }

    /**
     * @param f
     * @param s
     * @return signature which was replaced (see {@link Signature})
     */
    public Signature replaceSignatureForSymbol(String f, Signature s) {
        return this.typeAssumption.put(f, s);
    }

    /**
     * @param f
     * @return signature which was removed (see {@link Signature})
     */
    public Signature removeSignatureForSymbol(String f) {
        return this.typeAssumption.remove(f);
    }

    public Signature getSignatureForSymbol(String f) {
        return this.typeAssumption.get(f);
    }

    /*
     * (non-Javadoc)
     *
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.typeAssumption == null) ? 0 : this.typeAssumption.hashCode());
        return result;
    }

    /*
     * (non-Javadoc)
     *
     * @see java.lang.Object#equals(java.lang.Object)
     */
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
        final TypeAssumption other = (TypeAssumption) obj;
        if (this.typeAssumption == null) {
            if (other.typeAssumption != null) {
                return false;
            }
        }
        else if (!this.typeAssumption.equals(other.typeAssumption)) {
            return false;
        }
        return true;
    }

    /*
     * (non-Javadoc)
     *
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        StringBuilder buffer = new StringBuilder();
        for (Map.Entry<String, Signature> entry : this.typeAssumption.entrySet()) {
            buffer.append(entry.getKey());
            buffer.append(" :: ");
            buffer.append(entry.getValue());
            buffer.append("\n");
        }
        return buffer.toString();
    }

    /**
     * Applies substitution to the current type assumption
     *
     * @param sub
     */
    public void applySubstitution(TRSSubstitution sub) {
        for (Map.Entry<String, Signature> entry : this.typeAssumption.entrySet()) {
            entry.getValue().applySubstitution(sub);
        }
    }

    /**
     * @return the set of all type variables. Needed for computing the sorts
     */
    public Set<TRSVariable> getTypeVariables() {
        Set<TRSVariable> typeVars = new LinkedHashSet<TRSVariable>();
        for (Map.Entry<String, Signature> entry : this.typeAssumption.entrySet()) {
            typeVars.addAll(entry.getValue().getTypeVariables());
        }
        return typeVars;
    }

    /**
     * @param typeVar
     * @return symbols which are mapped to this output type variable
     */
    public Map<String, Integer> getSymbolsForTypeVariable(TRSVariable typeVar) {
        Map<String, Integer> symbols = new LinkedHashMap<String, Integer>();
        for (Map.Entry<String, Signature> entry : this.typeAssumption.entrySet()) {
            if (entry.getValue().getOutputType().equals(typeVar)) {
                symbols.put(entry.getKey(), entry.getValue().getInputTypes().size());
            }
        }
        return symbols;
    }
}
