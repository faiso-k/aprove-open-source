package aprove.input.Programs.prolog.structure;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;

/**
 * Represents a number in Prolog.<br><br>
 *
 * Created: May 5, 2006<br>
 * Last modified: Dec 13, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologNumber extends PrologTerm {

    /**
     * Constructs a new PrologNumber with the specified name.
     * @param name The number's name.
     */
    public PrologNumber(final String name) {
        super(name);
    }

    @Override
    public PrologTerm add(final int i, final PrologTerm term) {
        throw new UnsupportedOperationException("Cannot add arguments to numbers!");
    }

    @Override
    public PrologTerm add(final PrologTerm term) {
        throw new UnsupportedOperationException("Cannot add arguments to numbers!");
    }

    @Override
    public boolean equals(final Object o) {
        if (super.equals(o)) {
            return ((PrologTerm) o).isNumber();
        }
        return false;
    }

    @Override
    public int hashCode() {
        return 103 * this.getName().hashCode();
    }

    @Override
    public boolean isAtom(final Set<FunctionSymbol> preds) {
        return false;
    }

    @Override
    public boolean isNumber() {
        return true;
    }

    @Override
    public PrologTerm rename(final String oldName, final String newName, final int arity) {
        if (arity == 0 && this.getName().equals(oldName)) {
            return new PrologNumber(newName);
        } else {
            return this;
        }
    }

    @Override
    public PrologTerm replaceName(final String name) {
        return new PrologNumber(name);
    }

    @Override
    public PrologTerm replacePredicates(final Collection<? extends FunctionSymbol> preds, final PrologTerm term) {
        return this;
    }

    @Override
    public PrologTerm walk(final ReplacementWalker walker) {
        if (walker.isApplicable(this)) {
            return walker.replace(this);
        } else {
            return this;
        }
    }

}
