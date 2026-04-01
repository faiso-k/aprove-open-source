package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Some witness for nontermination, including a run.
 *
 * @author Marc Brockschmidt
 */
public abstract class NonTermWitness {
    /** The run that is part of the witness. */
    private final List<State> run;

    /**
     * @param r run that is part of the witness.
     */
    public NonTermWitness(final List<State> r) {
        this.run = r;
    }

    /**
     * Export the witness.
     * @param o some export util
     * @param level the verbosity level
     * @return a textual representation of the proof
     */
    public abstract String export(final Export_Util o, final VerbosityLevel level);

    /**
     * @return the run that is part of this witness.
     */
    public List<State> getRun() {
        return this.run;
    }

    /**
     * Export the witness.
     * @param sb the StringBuilder to export to.
     * @param o some export util
     * @return a textual representation of the proof
     */
    public String export(final StringBuilder sb, final Export_Util o) {
        int i = 0;
        for (final State s : this.run) {
            sb.append(i++).append(":").append(o.preFormatted(o.escape(s.toString(true, true))));
        }
        return sb.toString();
    }
}
