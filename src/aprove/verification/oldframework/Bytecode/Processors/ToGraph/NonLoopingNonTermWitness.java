package aprove.verification.oldframework.Bytecode.Processors.ToGraph;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Some witness for nontermination, including a run, the set of interesting
 * references at the loop head and a formula that was proven to be UNSAT.
 *
 * @author Marc Brockschmidt
 */
public class NonLoopingNonTermWitness extends NonTermWitness {
    /** The set of interesting references at the loop head. */
    private final Set<AbstractVariableReference> interestingRefs;
    /** The formula describing the integer constraints in the loop. */
    private final Formula<SMTLIBTheoryAtom> loopFormula;

    /**
     * The state at the start of the loop.
     */
    private final State loopStart;

    /**
     * @param run run that is part of the witness.
     * @param intRefs the set of interesting references at the loop head.
     * @param formula the formula describing the integer constraints in the
     * loop.
     * @param loopStartState the state at the start of the loop
     */
    public NonLoopingNonTermWitness(final List<State> run,
            final Set<AbstractVariableReference> intRefs,
            final Formula<SMTLIBTheoryAtom> formula, final State loopStartState) {
        super(run);
        this.interestingRefs = intRefs;
        this.loopFormula = formula;
        this.loopStart = loopStartState;
    }

    /** {@inheritDoc} */
    @Override
    public String export(final Export_Util o, final VerbosityLevel level) {
        final StringBuilder sb = new StringBuilder();

        sb.append("Reached a loop using the following run: ")
          .append(o.newline());
        super.export(sb, o);

        sb.append("Start state of loop: ").append(o.newline());
        sb.append(o.preFormatted(o.escape(this.loopStart.toString(true, false))));
        sb.append(o.newline());

        sb.append("In the loop head node, references ")
          .append(this.interestingRefs.toString())
          .append(" were interesting.")
          .append(o.newline());

        sb.append("All methods calls in the loop body are side-effect free, hence they can be ignored.").append(
            o.newline());
        sb.append("By SMT, we could prove")
          .append(o.newline())
          .append(o.escape(this.loopFormula.toString()))
          .append(o.newline())
          .append("to be UNSAT. Consequently, the loop will not terminate.");

        return sb.toString();
    }

}
