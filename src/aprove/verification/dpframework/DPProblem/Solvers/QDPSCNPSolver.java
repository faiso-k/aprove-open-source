package aprove.verification.dpframework.DPProblem.Solvers;

import java.util.*;
import java.util.logging.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Uses the NP fragment of size-change.
 * Based on the setting of the TACAS'08 paper "Size Change Termination
 * with Global Ranking Functions" by Amir M. Ben-Amram and Michael Codish.
 *
 * There, the size change relation between the arguments of a function call
 * is given by the data, but the interpretation of the program states (~ DPs)
 * via a ranking function that depends on those arguments and the size change
 * between them is determined by a SAT solver. Several different candidate
 * classes for ranking functions are used here.
 *
 * As an extension, here we also allow to search for the reduction pair
 * that is used to determine the edges of the (local) size change graphs.
 * Thus, the order for the arguments and the level mapping for the
 * head symbols are encoded to the same SAT problem for simultaneous search.
 *
 * @author Carsten Fuhs
 */
public class QDPSCNPSolver implements QActiveSolver {

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Solvers.QDPSCNPSolver");

    private final SolverFactory baseOrderFactory;

    private final SatEngine engine;

    private final boolean max;
    private final boolean min;
    private final boolean ms;
    private final boolean dms;

    private final boolean plain;
    private final boolean plainRoot;
    private final boolean rootArg;
    private final boolean listArgs;

    public QDPSCNPSolver(SCNPFactory scnpFactory, SolverFactory baseOrderFactory,
            SatEngine engine, boolean max, boolean min, boolean ms, boolean dms,
            boolean plain, boolean plainRoot, boolean rootArg, boolean listArgs) {
        this.baseOrderFactory = baseOrderFactory;
        this.engine = engine;
        this.max = max;
        this.min = min;
        this.ms = ms;
        this.dms = dms;
        this.plain = plain;
        this.plainRoot = plainRoot;
        this.rootArg = rootArg;
        this.listArgs = listArgs;
    }

    @Override
    public QActiveOrder solveQActive(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R,
            boolean active, boolean allstrict, Abortion aborter)
                throws AbortionException {

        /* Outline:
         * - encode that exactly one of the possible encodings for
         *   comparisons of argument tuples must be used
         *   (and remember for the proof output which formula stands
         *   for which comparison)
         * - for each allowed comparison c:
         *   - for each rule F(s_1, ..., s_k) -> G(t_1, ..., t_n) \in P:
         *     * for each s_i, t_j:
         *       - encode s_i >= t_j and s_i > t_j to SAT
         *         so that we can use this information as prop. formulas
         *         for the encoding of the ranking function for F, G
         *         (note that in general s_i > t_j does not imply s_i >= t_j)
         *
         *     * encode the search for the tagged level mapping for F and G
         *       using comparison c to SAT, where we use the formulas for
         *       s_i >(=) t_j
         *
         *       Here we only make use of the abstract information of the
         *       relations between the s_i and t_j. Details on how to proceed
         *       here can be found in the TACAS'08 paper. We may omit
         *       "numerical" level mappings since those should be subsumed
         *       by the Dependency Graph processor, which one can apply at
         *       an earlier stage. "Plain" level mappings are a special case
         *       of "tagged" level mappings, but they can still be useful as
         *       an optional heuristic (just fix all tags to 0).
         *
         *     * store information for active cond of G in the process
         *       (-> depends on the arg filter of the level mapping of G)
         *
         * - for each entry (l -> r, qac) in R:
         *   * encode l >= r
         *   * get the encoding for the atoms of qac that depend on the
         *     SCNPOrderEncoder (do this only /after/ all the rules have been
         *     handled since some information needed for the first qac could
         *     only have been generated while encoding a later )
         *   * encode the whole qac and add conjunct "qac -> l >= r"
         *     to overall formula
         *
         * - feed the whole formula to the SAT solver of your choice
         *
         * - enjoy!
         *
         * In the process, make sure that the ranking function orients all
         * rules from P non-strictly and some rule from P strictly (if allstrict
         * is set, all rules from P must be oriented strictly).
         */

        long time = System.nanoTime();
        if (! this.isApplicable(P, R)) {
            return null;
        }
        if (P.size() == 1) {
            allstrict = true;
        }

        SCNPFullEncoder fullEnc = new SCNPFullEncoder(this.baseOrderFactory,
                this.engine, this.max, this.min, this.ms, this.dms,
                this.plain, this.plainRoot, this.rootArg, this.listArgs, P);
        aborter.checkAbortion();
        Formula<None> formula = fullEnc.encode(P, R, allstrict, aborter);
        long tDiff = System.nanoTime() - time;
        long total = tDiff;
        QDPSCNPSolver.log.log(Level.FINE, "Encoding SCNP to SAT: {0} ms", tDiff/1000000);

        time = System.nanoTime();
        int[] res;
        aborter.checkAbortion();
        SATChecker satChecker = this.engine.getSATChecker();
        try {
            res = satChecker.solve(formula, aborter);
        } catch (SolverException e) {
            return null;
        }
        tDiff = System.nanoTime()-time;
        total += tDiff;
        QDPSCNPSolver.log.log(Level.FINER, "SAT solving: {0} ms\n", tDiff/1000000);
        if (res != null) {
            aborter.checkAbortion();
            SCNPOrder scnpOrder = fullEnc.decode(res, aborter);
            return scnpOrder;
        }
        return null;
    }

    private boolean isApplicable(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R) {
        // TODO figure out more of the nasty "corner cases"!!

        if (! (this.max || this.min || this.ms || this.dms)) {
            QDPSCNPSolver.log.warning("Warning: Attempted to invoke QDPSCNP without any allowed ranking function! Aborting.\n");
            return false;
        }

        Set<? extends GeneralizedRule> rRules = R.keySet();
        Set<FunctionSymbol> tupleSymbols =
            aprove.verification.dpframework.BasicStructures.CollectionUtils.getTupleSymbols(P, rRules);

        // TODO be more liberal and use head symbols
        if (tupleSymbols == null) {
            // underlying DP problem does not satisfy tuple property
            return false;
        }

        if (! this.rootArg) {
            for (FunctionSymbol f : tupleSymbols) {
                if (f.getArity() == 0) {
                    // there is no argument with a size change!
                    // note that here actually numerical ranking functions /could/
                    // help, but the dependency graph processor should rather be
                    // used for such cases.
                    // TODO are there other cases where constant symbols can be
                    // handled sensibly?
                    return false;
                }
            }
        }
        return true;
    }
}
