package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

/**
 * Engine for minisatP, a MiniSAT 2 variant which uses CPU prefetching
 * instructions to improve performance on contemporary CPUs with cache
 * memory. Search path is not altered over the original MiniSAT 2.
 * Prefetching upgrades by Norbert Manthey. Techniques are described
 * in the LPAR-17 paper "Improving Resource-Unaware SAT Solvers" by
 * S. Hoelldobler, N. Manthey, and A. Saptawijaya (2010).
 *
 * @author fuhs
 */
public class MINISATPEngine extends SatEngine {

    private final boolean prefetchHeader; // prefetch clause header?
    private final boolean prefetchLists; // prefetch watch lists?

    private final boolean simp;

    @ParamsViaArgumentObject
    public MINISATPEngine(Arguments arguments) {
        super(arguments);
        this.prefetchHeader = arguments.prefetchHeader;
        this.prefetchLists = arguments.prefetchLists;
        this.simp = arguments.simp;
    }

    @Override
    public SATChecker getSATChecker() {
        return new MiniSATFileChecker(2,
                    this.simp, false, true, false,
                    false, true, false,
                    this.prefetchHeader, this.prefetchLists);
    }

    public static class Arguments extends SatEngine.Arguments {
        public boolean prefetchHeader = true;
        public boolean prefetchLists = true;
        public boolean simp = false;
    }

}
