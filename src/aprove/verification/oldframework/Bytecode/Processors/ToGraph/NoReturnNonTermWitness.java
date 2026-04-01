package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Some witness for nontermination due to no reachable return state. Includes a run to the call site (unless the
 * method without a return is main).
 *
 * @author Marc Brockschmidt
 */
public class NoReturnNonTermWitness extends NonTermWitness {
    /** The method without return state. */
    private final IMethod methodWithoutReturn;

    /**
     * @param run run that is part of the witness.
     * @param noReturnMethod The method without return state.
     */
    public NoReturnNonTermWitness(final List<State> run, final IMethod noReturnMethod) {
        super(run);
        this.methodWithoutReturn = noReturnMethod;
    }

    /** {@inheritDoc} */
    @Override
    public String export(final Export_Util o, final VerbosityLevel level) {
        final StringBuilder sb = new StringBuilder();

        sb.append("Symbolic evaluation of method ").append(this.methodWithoutReturn.toString()).append(
            " never reaches a method end (by explicit return or exception).").append(o.newline());

        if (this.getRun() == null) {
            sb.append("As this is the main method, we can conclude non-termination of the input program.");
        } else {
            sb.append("The method is called in the following run from the start state:").append(o.newline());
            super.export(sb, o);
        }

        return sb.toString();
    }
}
