package aprove.input.Utility;

import java.util.*;

import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A generic class to handle parse-errors.
 */

public class ParseErrors implements Iterable<ParseError> {

    private final ArrayList<ParseError> errors = new ArrayList<ParseError>();

    /** The error-level of the parse-error with the highest error-level.
     */
    protected int maxLevel;

    public ParseErrors() {
        super();
        this.maxLevel = 0;
    }

    public boolean add(ParseError o) {
        this.errors.add(o);
        int ol = o.getLevel();
        if (ol > this.maxLevel) {
            this.maxLevel = ol;
        }
        return true;
    }

    public int getMaxLevel() {
    return this.maxLevel;
    }

    public void clear() {
        this.errors.clear();
        this.maxLevel = 0;
    }

    public ParseError getFirst() {
        return this.errors.get(0);
    }

    /** Throws a runtime-exception if there is a parse-error with
     *  a level of at least ERROR.
     */
    public void throwOnError() throws RuntimeException {
        if (this.maxLevel < ParseError.ERROR) {
            return;
        }
        for (ParseError pe : this.errors) {
            if (pe.getLevel() >= ParseError.ERROR) {
                throw new RuntimeException(pe.toString());
            }
        }
    }

    public boolean addAll(ParseErrors c) {
        if (this.maxLevel < c.maxLevel) {
            this.maxLevel = c.maxLevel;
        }
        return this.errors.addAll(c.errors);
    }

    public boolean addAll(Collection<? extends ParseError> c) {
        for (ParseError pe : c) {
            int level = pe.getLevel();
            if (level > this.maxLevel) {
                this.maxLevel = level;
            }
            this.errors.add(pe);
        }
        return true;
    }

    public boolean isEmpty() {
        return this.errors.isEmpty();
    }

    @Override
    public Iterator<ParseError> iterator() {
        return new UnmodifiableIterator<ParseError>(this.errors.iterator());
    }

    @Override
    public String toString() {
        return "ParseErrors: " + this.errors.toString();
    }
}
