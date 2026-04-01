package aprove.input.Programs.prolog.structure;

import java.util.*;

import immutables.*;

/**
 * PrologCyclicTerm.<br><br>
 *
 * Created: Sep 14, 2008<br>
 * Last modified: Sep 14, 2008
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologCyclicTerm extends PrologTerm {

    /**
     * @author cryingshadow
     * Models a cyclic variable.
     */
    public static final class PrologCyclicVariable extends PrologTerm {

        /**
         * Standard constructor.
         */
        private PrologCyclicVariable() {
            super("**");
        }

        /**
         * Creates a deep copy.
         * @return A deep copy.
         */
        public PrologCyclicVariable deepCopy() {
            return this;
        }

        @Override
        public boolean equals(final Object o) {
            return o instanceof PrologCyclicVariable;
        }

        @Override
        public int hashCode() {
            return 421984;
        }

    }

    /**
     * There can be only one... Up to now...
     */
    public static final PrologCyclicVariable CYCLIC_VARIABLE = new PrologCyclicVariable();

    /**
     * The term by which the cyclic variable is to be replaced.
     */
    private final PrologTerm cycle;

    /**
     * TODO
     */
    private boolean showCycle;

    /**
     * Creates a new PrologCyclicTerm from the specified term which contains the variable cycleVar.
     * @param cycleParam The term representing the cyclic term.
     * @param cycleVar The cyclic variable in the term.
     */
    public PrologCyclicTerm(final PrologTerm cycleParam, final PrologVariable cycleVar) {
        super(cycleParam.getName());
        this.cycle = cycleParam.replaceAll(cycleVar, PrologCyclicTerm.CYCLIC_VARIABLE);
        this.showCycle = true;
    }

    /**
     * Shortcut for convenience (the specified term already contains its cyclic variable).
     * @param cycleParam The cyclic term.
     */
    private PrologCyclicTerm(final PrologTerm cycleParam) {
        super(cycleParam.getName());
        this.cycle = cycleParam;
        this.showCycle = true;
    }

    @Override
    public PrologTerm add(final int index, final PrologTerm t) {
        throw new UnsupportedOperationException("You cannot add arguments to cyclic terms!");
    }

    @Override
    public PrologTerm add(final PrologTerm t) {
        throw new UnsupportedOperationException("You cannot add arguments to cyclic terms!");
    }

    @Override
    public PrologTerm applySubstitution(final Map<? extends PrologVariable, ? extends PrologTerm> substitution) {
        return this.cycle.applySubstitution(substitution);
    }

    @Override
    public boolean contains(final PrologTerm term) {
        if (term.isCyclic()) {
            //TODO
            return false;
        }
        return false;
    }

    @Override
    public ImmutableList<PrologTerm> getArguments() {
        // TODO ???
        final PrologTerm copy = this.cycle.replaceAll(PrologCyclicTerm.CYCLIC_VARIABLE, this);
        return copy.getArguments();
    }

    /**
     * Returns the cyclic part of this cyclic term.
     * @return The cyclic part of this cyclic term.
     */
    public PrologTerm getCycle() {
        return this.cycle;
    }

    //TODO equals

    @Override
    public int hashCode() {
        //TODO hashCode in all PrologTerms only from first symbol
        return this.cycle.createFunctionSymbol().hashCode() * 101 + 13;
    }

    @Override
    public String toString() {
        if (this.showCycle) {
            this.showCycle = false;
            final String res = this.cycle.toString();
            this.showCycle = true;
            return res;
        } else {
            return "**";
        }
    }

}
