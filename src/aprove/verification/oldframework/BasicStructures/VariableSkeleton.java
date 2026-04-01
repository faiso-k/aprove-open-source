package aprove.verification.oldframework.BasicStructures;

import java.util.*;

import aprove.prooftree.Export.Utility.*;

/**
 * Implements/overrides some basic methods.
 * @author cryingshadow
 * @version $Id$
 */
public abstract class VariableSkeleton implements Variable {

    /**
     * The name.
     */
    private final String name;

    /**
     * @param n The name.
     */
    public VariableSkeleton(String n) {
        this.name = n;
    }

    @Override
    public boolean equals(Object obj) {
        return Variable.equals(this, obj);
    }

    @Override
    public String export(Export_Util eu) {
        return eu.export(this.toString());
    }

    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public Set<? extends Variable> getVariables() {
        return Collections.singleton(this);
    }

    @Override
    public int hashCode() {
        return Variable.hashCode(this);
    }

    @Override
    public String toString() {
        return this.getName();
    }

}
