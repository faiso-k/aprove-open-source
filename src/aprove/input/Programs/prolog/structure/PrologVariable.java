package aprove.input.Programs.prolog.structure;

import java.util.*;

import aprove.input.Programs.prolog.processors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Represents a variable in Prolog.<br><br>
 *
 * Created: May 5, 2006<br>
 * Last modified: Aug 19, 2015
 *
 * @author cryingshadow
 * @version $Id$
 */
public abstract class PrologVariable extends PrologTerm {

    /**
     * Constructs a new PrologVariable with the specified name.
     * @param name The variable's name.
     */
    public PrologVariable(final String name) {
        super(name);
    }

    @Override
    public PrologTerm add(final int i, final PrologTerm term) {
        throw new UnsupportedOperationException("Cannot add arguments to variables!");
    }

    @Override
    public PrologTerm add(final PrologTerm term) {
        throw new UnsupportedOperationException("Cannot add arguments to variables!");
    }

    @Override
    public PrologTerm applySubstitution(final Map<? extends PrologVariable, ? extends PrologTerm> substitution) {
        if (substitution.containsKey(this)) {
            return substitution.get(this);
        } else {
            return this;
        }
    }

    @Override
    public boolean containsOnlyVariablesFrom(final Set<PrologVariable> vars) {
        return vars.contains(this);
    }

    @Override
    public VariableSet createSetOfAllVariables() {
        final VariableSet res = new VariableSet();
        res.add(this);
        return res;
    }

    @Override
    public boolean equals(final Object o) {
        if (super.equals(o) && o instanceof PrologVariable) {
            return this.equalsVariable((PrologVariable) o);
        }
        return false;
    }

    @Override
    public String export(final Export_Util o) {
        return o.fontcolor(o.export(this.getName()), Color.RED);
    }

    @Override
    public String export(final Export_Util o, final Set<FunctionSymbol> preds) {
        return o.fontcolor(o.export(this.getName()), Color.RED);
    }

    @Override
    public Set<Occurrence> getAllOccurrencesOfVariables() {
        final Set<Occurrence> res = new LinkedHashSet<Occurrence>();
        res.add(new Occurrence());
        return res;
    }

    @Override
    public abstract int hashCode();

    @Override
    public boolean isAtom(final Set<FunctionSymbol> preds) {
        return false;
    }

    @Override
    public boolean isConstant() {
        return false;
    }

    @Override
    public boolean isConstructorTerm(final Set<FunctionSymbol> preds) {
        return true;
    }

    @Override
    public boolean isGround() {
        return false;
    }

    @Override
    public boolean isVariable() {
        return true;
    }

    @Override
    public abstract PrologTerm rename(String oldName, String newName, int arity);

    @Override
    public PrologTerm replaceAll(final PrologTerm oldTerm, final PrologTerm newTerm) {
        if (this.equals(oldTerm)) {
            return newTerm;
        } else {
            return this;
        }
    }

    @Override
    public abstract PrologTerm replaceName(String name);

    @Override
    public PrologTerm replacePredicates(final Collection<? extends FunctionSymbol> preds, final PrologTerm term) {
        return this;
    }

    @Override
    public String toSExpression() {
        return this.getName();
    }

    @Override
    public TRSTerm toTerm() {
        return TRSTerm.createVariable(this.getName());
    }

    @Override
    public TRSTerm toTerm(final PrologFNG fridge) {
        return TRSTerm.createVariable(this.getName());
    }

    @Override
    public PrologTerm walk(final ReplacementWalker walker) {
        if (walker.isApplicable(this)) {
            return walker.replace(this);
        } else {
            return this;
        }
    }

    /**
     * Helper method to compare the variable type.
     * @param v The variable to compare the type with.
     * @return True, if the specified variable has the same type as
     *         this variable. False otherwise.
     */
    protected abstract boolean equalsVariable(PrologVariable v);

}
