package aprove.verification.oldframework.Input;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.oldframework.Logic.*;
import immutables.*;

/**
 * Handling modes for obligations.
 * @author dickmeis
 * @version $Id$
 */
public enum HandlingMode implements Exportable, Immutable {

    /**
     * Derivational complexity is the length of the longest possible derivation in a TRS in relation to the size of the
     * start term used for that derivation.
     */
    DerivationalComplexity("Derivational Complexity"),

    /**
     * Determinacy is given for a logic program if each query in the set of start queries results in at most one answer
     * substitution.
     */
    Determinacy("Determinacy"),

    /**
     * Memory safety is given if no unallocated memory is accessed by the program.
     */
    MemorySafety("Memory Safety"),

    /**
     * Innermost runtime complexity is like derivational complexity, but restricted to innermost derivations and to
     * start terms with exactly one defined symbol, which is at the root position.
     */
    RuntimeComplexity("Innermost Runtime Complexity"),

    /**
     * The cost model is specified by the user, e.g., by assigning costs to java methods via method summaries.
     */
    UserDefined("user defined cost model"),

    /**
     * How much space will the analyzed program allocate?
     */
    SpaceComplexity("Space Complexity"),

    /**
     * How big is the the result of the analyzed program going to be?
     */
    SizeComplexity("Result Size"),

    /**
     * Compute a summary for the analyzed method which can be reused for later runs of AProVE.
     */
    MethodSummary("Method Summary"),

    /**
     * Satisfiability (possibly modulo some theory).
     */
    Satisfiability("Satisfiability"),

    /**
     * Termination.
     */
    Termination("Termination"),

    /**
     * TODO: docu
     */
    TheoremProver("Proof");

    /**
     * The name of this handling mode.
     */
    private final String name;

    /**
     * @param nameParam The name of this handling mode.
     */
    private HandlingMode(String nameParam) {
        this.name = nameParam;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Export.Utility.Exportable#export(aprove.prooftree.Export.Utility.Export_Util)
     */
    @Override
    public String export(Export_Util eu) {
        return this.getName();
    }

    /**
     * @return The name of this handling mode.
     */
    public String getName() {
        return this.name;
    }

    public static Optional<HandlingMode> valueOfIgnoreCase(String s) {
        for (HandlingMode m: HandlingMode.values()) {
            if (s.equalsIgnoreCase(m.toString())) {
                return Optional.of(m);
            }
        }
        return Optional.empty();
    }

    /**
     * @param concrete for complexity-related handling modes, this flag specifies if the implication
     *                 should also propagate concrete (instead of just asymptotic) bounds.
     */
    public Implication equivalent(boolean concrete) {
        switch (this) {
            case RuntimeComplexity:
            case SpaceComplexity:
            case UserDefined:
            case SizeComplexity:
            case MethodSummary:
                return concrete ? BothBounds.forConcreteBounds() : BothBounds.create();
            default:
                return YNMImplication.EQUIVALENT;
        }
    }

    /**
     * @see HandlingMode#equivalent(boolean)
     */
    public Implication overapproximating(boolean concrete) {
        switch (this) {
            case RuntimeComplexity:
            case SpaceComplexity:
            case UserDefined:
            case SizeComplexity:
                return concrete ? UpperBound.forConcreteBounds() : UpperBound.create();
            default: return YNMImplication.SOUND;
        }
    }

    /**
     * @see HandlingMode#equivalent(boolean)
     */
    public Implication underapproximating(boolean concrete) {
        switch (this) {
            case RuntimeComplexity:
            case SpaceComplexity:
            case UserDefined:
            case SizeComplexity:
                return concrete ? LowerBound.forConcreteBounds() : LowerBound.create();
            default: return YNMImplication.COMPLETE;
        }
    }

}
