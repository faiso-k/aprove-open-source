package aprove.verification.oldframework.IntTRS.Ranking;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Represents a well-founded ranking relation.
 * @author Matthias Hoelzel
 */
class Ranking extends TransitionRelation {
    /**
     * Stores the positions of the left variables.
     */
    private final LinkedHashMap<String, Integer> leftVariablePositions;

    /**
     * Stores the positions of the right variables.
     */
    private final LinkedHashMap<String, Integer> rightVariablePositions;

    /**
     * Constructor!
     * @param pcs the ranking constraints
     * @param symbol function symbol
     * @param startVars start variables
     * @param endVars end variables
     * @param included transition relation
     * @param eliminateVariables true, iff free variables should be eliminated
     * @param abortion some aborter
     * @throws AbortionException can be aborted
     */
    Ranking(
        final PCS pcs,
        final FunctionSymbol symbol,
        final List<TRSVariable> startVars,
        final List<TRSVariable> endVars,
        final TransitionRelation included,
        final boolean eliminateVariables,
        final Abortion abortion) throws AbortionException
    {
        super(
            pcs,
            symbol,
            startVars,
            symbol,
            endVars,
            Collections.singletonList(included),
            eliminateVariables,
            abortion);

        this.leftVariablePositions = new LinkedHashMap<>(symbol.getArity());
        this.rightVariablePositions = new LinkedHashMap<>(symbol.getArity());

        final Iterator<TRSVariable> leftVariableIterator = startVars.iterator();
        final Iterator<TRSVariable> rightVariableIterator = endVars.iterator();
        for (int position = 0; position < symbol.getArity(); position++) {
            final String leftNext = leftVariableIterator.next().getName();
            final String rightNext = rightVariableIterator.next().getName();

            assert !this.leftVariablePositions.containsKey(leftNext)
                && !this.rightVariablePositions.containsKey(rightNext) : "Invalid ranking: Variable occurs twice!";

            this.leftVariablePositions.put(leftNext, position);
            this.rightVariablePositions.put(rightNext, position);
        }
    }

    @Override
    public boolean isCertainlyWellFounded() {
        return true;
    }

    @Override
    public boolean containsRelation(final TransitionRelation other) throws AbortionException {
        assert other != null : "TransitionRelation should not be null!";
        if (!(this.getStartSymbol().equals(other.getStartSymbol()) && this.getEndSymbol().equals(other.getEndSymbol())))
        {
            return false;
        }

        for (final GEConstraint constraint : this.getPCS().getConstraints()) {
            // Create renaming:
            final Set<String> variables = constraint.getPoly().getVariables();
            final Map<String, VarPolynomial> renaming = new LinkedHashMap<>(variables.size());
            for (final String variable : variables) {
                final TRSVariable correspondingVariable;
                if (this.leftVariablePositions.containsKey(variable)) {
                    correspondingVariable = other.getStartVariables().get(this.leftVariablePositions.get(variable));
                } else if (this.rightVariablePositions.containsKey(variable)) {
                    correspondingVariable = other.getEndVariables().get(this.rightVariablePositions.get(variable));
                } else {
                    assert false : "Free variable in ranking detected!!";
                    return false;
                }

                renaming.put(variable, VarPolynomial.createVariable(correspondingVariable.getName()));
            }

            // Get renamed version:
            final GEConstraint toCheck = constraint.substitute(renaming, this.aborter);

            if (!other.getPCS().checkImplicationDestructive(toCheck)) {
                return false;
            }
        }
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + ((this.leftVariablePositions == null) ? 0 : this.leftVariablePositions.hashCode());
        result = prime * result + ((this.rightVariablePositions == null) ? 0 : this.rightVariablePositions.hashCode());
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (!super.equals(obj)) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final Ranking other = (Ranking) obj;
        if (this.leftVariablePositions == null) {
            if (other.leftVariablePositions != null) {
                return false;
            }
        } else if (!this.leftVariablePositions.equals(other.leftVariablePositions)) {
            return false;
        }
        if (this.rightVariablePositions == null) {
            if (other.rightVariablePositions != null) {
                return false;
            }
        } else if (!this.rightVariablePositions.equals(other.rightVariablePositions)) {
            return false;
        }
        return (this.getStartSymbol().equals(other.getStartSymbol())
            && this.getEndSymbol().equals(other.getEndSymbol())
            && this.getStartVariables().equals(other.getStartVariables())
            && this.getEndVariables().equals(other.getEndVariables()) && this.getPCS().equals(other.getPCS()));
    }
}
