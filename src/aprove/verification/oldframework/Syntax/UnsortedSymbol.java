package aprove.verification.oldframework.Syntax;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

/**
 * A unsorted symbol. This is the base class for sort symbols
 * and sorted symbols.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public abstract class UnsortedSymbol implements Checkable, java.io.Serializable, HasName {

    /**
     * Name of this symbol.
     */
    protected String name;

    /* CONSTRUCTORS */

    public UnsortedSymbol() {
    }

    /**
     * Class constructor specifying name. As this is
     * an abstract class this is strictly for use by subclasses.
     */
    protected UnsortedSymbol(String name) {
    this.name = name;
    }

    /* ACCESSORS */

    /**
     * Gets the name of this symbol.
     * @return Name of this symbol.
     */
    @Override
    public String getName() {
        return this.name;
    }

    /**
     * Set the name of this symbol.
     */
    public void setName(String newname) {
        this.name = newname;
    }

    /**
     * Returns a string representation of this symbol,
     * i.e. the name of the symbol.
     * @return String representation of this symbol.
     */
    @Override
    public String toString() {
    return this.name;
    }

    /**
     * Returns an extremely verbose string representation of this symbol.<BR>
     * <B>DEBUG</B>
     */
    public abstract String verboseToString();

    /* MISC. METHODS */

    /**
     * Compares the specified symbol with this symbol for equality.
     * @param o Symbol to be compared for equality with this symbol.
     * @return Truth if the specified symbol is equal to this symbol.
     */
    @Override
    public boolean equals(Object o) {

    if (!(o instanceof UnsortedSymbol)) {
        return false;
    }

    UnsortedSymbol symbol = (UnsortedSymbol)o;
    return this.name.equals(symbol.name);

    }

    /**
     * Calculates a hash code based on the symbol's name.
     * @return Hash code of the symbol's name.
     */
    @Override
    public int hashCode() {

    return this.name.hashCode();

    }

    /* CHECKABLE */

    @Override
    public void check() {
    this.check(new HashSet());
    }

    @Override
    public void check(Set checked) {
    if (!checked.contains(this)) {
        checked.add(this);
        if (this.name ==  null) {
        throw new RuntimeException("name must not be null");
        }
        if (this.name.equals("")) {
        throw new RuntimeException("name must not be empty");
        }
    }
    }

}
