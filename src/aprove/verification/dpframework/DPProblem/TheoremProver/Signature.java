package aprove.verification.dpframework.DPProblem.TheoremProver;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * A signature is of the form a1,..,an -> b and describes typing/sorting of a
 * term.
 *
 * @author micpar
 * @version $Id$
 */

public class Signature {
    /*
     * attributes
     */
    private List<TRSTerm> inputTypes = null;
    private TRSTerm       outputType = null;

    /**
     * @return input types of term
     */
    public List<TRSTerm> getInputTypes() {
        return this.inputTypes;
    }

    /**
     * @param inputTypes
     */
    public void setInputTypes(List<TRSTerm> inputTypes) {
        this.inputTypes = inputTypes;
    }

    /**
     * @return output type of term
     */
    public TRSTerm getOutputType() {
        return this.outputType;
    }

    /**
     * @param outputType
     */
    public void setOutputType(TRSTerm outputType) {
        this.outputType = outputType;
    }

    /**
     * Creates a new Signature
     *
     * @param inputTypes
     * @param outputType
     */
    public Signature(List<TRSTerm> inputTypes, TRSTerm outputType) {
        this.inputTypes = inputTypes;
        this.outputType = outputType;
    }

    /**
     * @param index
     * @return input type term at index position
     */
    public TRSTerm getInputTypeAtIndex(int index) {
        if (index < this.inputTypes.size()) {
            return this.inputTypes.get(index);
        }
        return null;
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
        result = prime * result + ((this.inputTypes == null) ? 0 : this.inputTypes.hashCode());
        result = prime * result + ((this.outputType == null) ? 0 : this.outputType.hashCode());
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
        final Signature other = (Signature) obj;
        if (this.inputTypes == null) {
            if (other.inputTypes != null) {
                return false;
            }
        }
        else if (!this.inputTypes.equals(other.inputTypes)) {
            return false;
        }
        if (this.outputType == null) {
            if (other.outputType != null) {
                return false;
            }
        }
        else if (!this.outputType.equals(other.outputType)) {
            return false;
        }
        return true;
    }

    /**
     * @param index
     * @param element
     * @return true if operation was successful
     */
    public boolean setInputTypeAtIndex(int index, TRSTerm element) {
        if (index < this.inputTypes.size()) {
            this.inputTypes.set(index, element);
            return true;
        }
        return false;
    }

    /*
     * (non-Javadoc)
     *
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        StringBuilder buffer = new StringBuilder();
        for (TRSTerm term : this.inputTypes) {
            buffer.append(term);
            buffer.append(", ");
        }
        if (this.inputTypes.size() > 0) {
            buffer.deleteCharAt(buffer.length() - 1);
            buffer.deleteCharAt(buffer.length() - 1);
            buffer.append(" -> ");
        }
        buffer.append(this.outputType);
        return buffer.toString();
    }

    /**
     * Applies substitution to signature
     *
     * @param sub
     */
    public void applySubstitution(TRSSubstitution sub) {
        List<TRSTerm> temp = new Vector<TRSTerm>(this.inputTypes);
        this.inputTypes.clear();
        for (TRSTerm term : temp) {
            this.inputTypes.add(term.applySubstitution(sub));
        }
        this.outputType = this.outputType.applySubstitution(sub);
    }

    /**
     * @return set of type variables. A signature consists of type variables in
     *         my (micpar) context
     */
    public Set<TRSVariable> getTypeVariables() {
        Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>();
        for (TRSTerm t : this.inputTypes) {
            if (t.isVariable()) {
                vars.add((TRSVariable) t);
            }
        }
        if (this.outputType.isVariable()) {
            vars.add((TRSVariable) this.outputType);
        }
        return vars;
    }
}
