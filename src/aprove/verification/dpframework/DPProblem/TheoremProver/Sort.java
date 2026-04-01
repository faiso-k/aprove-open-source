package aprove.verification.dpframework.DPProblem.TheoremProver;

import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * A Sort has a name and constructor and a specific error constant
 *
 * @author micpar
 * @version $Id$
 */

public class Sort {

    /*
     * attributes
     */
    private String                       name         = "default";
    private FunctionSymbol               witnessTerm  = null;
    private ImmutableSet<FunctionSymbol> constructors = null;

    /**
     * @param name
     * @param constructors
     * @param error
     */
    public Sort(String name, ImmutableSet<FunctionSymbol> constructors, FunctionSymbol witnessTerm) {
        super();
        this.name = name;
        this.constructors = constructors;
        this.witnessTerm = witnessTerm;
    }

    /**
     * @return name of sort
     */
    public String getName() {
        return this.name;
    }

    /**
     * @return constructors of sort
     */
    public ImmutableSet<FunctionSymbol> getConstructors() {
        return this.constructors;
    }

    /**
     * @return witnessTerm
     */
    public FunctionSymbol getWitnessTerm() {
        return this.witnessTerm;
    }

    /*
     * (non-Javadoc)
     *
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        StringBuilder buffer = new StringBuilder();
        buffer.append(this.name);
        buffer.append(this.constructors);
        return buffer.toString();
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
        result = prime * result + ((this.constructors == null) ? 0 : this.constructors.hashCode());
        result = prime * result + ((this.name == null) ? 0 : this.name.hashCode());
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
        final Sort other = (Sort) obj;
        if (this.constructors == null) {
            if (other.constructors != null) {
                return false;
            }
        }
        else if (!this.constructors.equals(other.constructors)) {
            return false;
        }
        if (this.name == null) {
            if (other.name != null) {
                return false;
            }
        }
        else if (!this.name.equals(other.name)) {
            return false;
        }
        return true;
    }

}
