package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Some witness for nontermination, including a run and two states that are
 * repeating.
 *
 * @author Marc Brockschmidt
 */
public class LoopingNonTermWitness extends NonTermWitness {
    /** First occurrence of the repeating state. */
    private final int firstOccur;
    /** Second occurrence of the repeating state. */
    private final int secondOccur;
    /** Interesting positions used in the proof. */
    private final Set<StatePosition> interestingPositions;

    /**
     * @param r run that is part of the witness.
     * @param firstO first occurrence of the repeating state.
     * @param secondO second occurrence of the repeating state.
     */
    public LoopingNonTermWitness(final List<State> r, final int firstO, final int secondO,
            final Set<StatePosition> interestingPos) {
        super(r);
        this.firstOccur = firstO;
        this.secondOccur = secondO;
        this.interestingPositions = interestingPos;
    }

    /** {@inheritDoc} */
    @Override
    public String export(final Export_Util o, final VerbosityLevel level) {
        final StringBuilder sb = new StringBuilder();
        sb.append("Constructed a run with a repetition. States ").append(this.firstOccur).append(" and ").append(
            this.secondOccur).append(" are repetitions");
        if (this.interestingPositions != null) {
            sb.append(" (when considering only the interesting positions ").append(this.interestingPositions).append(
                ")");
        }
        sb.append(".").append(o.newline());

        super.export(sb, o);

        return sb.toString();
    }
}
