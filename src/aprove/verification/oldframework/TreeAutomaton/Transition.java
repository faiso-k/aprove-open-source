package aprove.verification.oldframework.TreeAutomaton;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * @author Marcel Klinzing
 */
public class Transition<S extends HasArity, Z> {
    private final S lhsFunctionSymbol;
    private final ImmutableList<Z> lhsStateParameters;
    private final Z rhsState;

    //computed / cached values
    private final int hashCode;

    public Transition(final S lhsFunctionSymbol, final ImmutableList<Z> lhsStateParameters,
            final Z rhsState) {
        if (Globals.useAssertions) {
            this.checkConstrArg(lhsFunctionSymbol, lhsStateParameters, rhsState);
        }
        this.lhsFunctionSymbol = lhsFunctionSymbol;
        this.lhsStateParameters = lhsStateParameters;
        this.rhsState = rhsState;

        int hash = lhsFunctionSymbol.hashCode() * 82808;
        for (final Z stateParam : lhsStateParameters) {
            hash += stateParam.hashCode() * 133998;
        }
        hash += rhsState.hashCode() * 34510;

        this.hashCode = hash;
    }

    private void checkConstrArg(final S lhsFunctionSymbol,
            final ImmutableList<Z> lhsStateParameters, final Z rhsState) {
        assert (lhsFunctionSymbol != null);
        assert (lhsStateParameters != null);
        assert (lhsFunctionSymbol.getArity() == lhsStateParameters.size());
        assert (rhsState != null);
    }

    @Override
    public String toString() {
        String out = "" + this.lhsFunctionSymbol + "(";
        for (Z z : this.lhsStateParameters) {
            out += z + ",";
        }
        out = out.substring(0, out.length() - 1);
        out += ")" + "-->" + this.rhsState;
        return out;
        /*return "Transition [lhsFunctionSymbol=" + this.lhsFunctionSymbol + "(" + ", lhsStateParameters=" + this.lhsStateParameters + ", rhsState="
            + this.rhsState + "]";*/
    }

    public static <S extends HasArity, Z> Transition<S, Z> create(final S lhsFunctionSymbol, final List<Z> lhsStateParameters,
            final Z rhsState) {
        ImmutableList<Z> iLhsStateParameters = ImmutableCreator.create(lhsStateParameters);
        return new Transition<S, Z>(lhsFunctionSymbol, iLhsStateParameters, rhsState);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public boolean equals(final Object other) {
        if (this == other) {
            return true;
        }
        if (other instanceof Transition<?, ?>) {
            final Transition<?, ?> t = (Transition<?, ?>) other;

            return this.hashCode == t.hashCode
                && this.lhsFunctionSymbol.equals(t.lhsFunctionSymbol)
                && this.lhsStateParameters.equals(t.lhsStateParameters)
                && this.rhsState.equals(t.rhsState);
        }

        return false;
    }

    public boolean equalsInLhs(Transition<S, Z> trans) {
        if (this.lhsFunctionSymbol.equals(trans.getLhsFunctionSymbol())) {
            int index = 0;
            for (Z state : this.lhsStateParameters) {
                if (!state.equals(trans.getLhsStateParameters().get(index))) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    public S getLhsFunctionSymbol() {
        return this.lhsFunctionSymbol;
    }

    public ImmutableList<Z> getLhsStateParameters() {
        return this.lhsStateParameters;
    }

    public Z getRhsState() {
        return this.rhsState;
    }
}
