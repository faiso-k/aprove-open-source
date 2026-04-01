package aprove.verification.dpframework.Utility.NonLoop.heuristic;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;

/**
 * <b>This heuristic has to be re-worked before use</b> <br>
 * <br>
 * This class represents a heuristic<br>
 * (c.f. "Proving and Disproving Higher Order Functions"):
 * <ul>
 * <li>If P \cup R is right- and not left-linear, then use forward narrowing</li>
 * <li>Otherwise, we use backward narrowing. If P \cup R is not left-linear,
 * then moreover we also permit narrowing steps in variables.</li>
 * <li><b>Not implemented yet:</b>Moreover, to obtain a ﬁnite search space, we
 * use an upper bound on the number of times that a rule from P ∪ R can be used
 * for narrowing.</li>
 * <li>Pattern-Narrowing is allowed at any time.</li>
 * </ul>
 *
 * @author Tim Enger
 */
public class SimpleNonLoopHeuristic implements NonLoopHeurisitic {

    /* which narrowing techniques are allowed */
    private boolean forwardNarrowing;
    private boolean backwardNarrowing;
    private boolean allowVarPos;

    /* depth limit for narrowing */
    private final int forwardLimit;
    private final int backwardLimit;

    /* level from which on R should be processed */
    private final int processR;

    /* actual "depth" of narrowing */
    private int narrowingDepth;

    public SimpleNonLoopHeuristic(final QDPProblem qdp, final int forwardLimit, final int backwardLimit,
            final int processR, final Logger log) {
        final Set<Rule> allRules = new HashSet<Rule>(qdp.getP());
        allRules.addAll(qdp.getR());

        this.forwardLimit = forwardLimit;
        this.backwardLimit = backwardLimit;
        this.processR = processR;

        this.narrowingDepth = 0;

        final boolean rightLinear = CollectionUtils.isRightLinear(allRules);
        final boolean leftLinear = CollectionUtils.isLeftLinear(allRules);

        this.forwardNarrowing = false;
        this.backwardNarrowing = false;
        this.allowVarPos = false;

        if (rightLinear && !leftLinear) {
            if (Globals.DEBUG_NEX) {
                System.err.println("Heuristic: Decided to only use " + " Forward Narrowing");
            }
            log.info("Heuristic: Decided to only use Forward Narrowing");
            this.forwardNarrowing = true;
        } else {
            this.backwardNarrowing = true;

            if (!leftLinear) {
                this.allowVarPos = true;
                if (Globals.DEBUG_NEX) {
                    System.err.println("Heuristic: Decided to only use"
                        + " Backward Narrowing and permit narrowing into" + " variables.");
                }
                log.info("Heuristic: Decided to only use Backward " + "Narrowing and permit narrowing into variables.");
            } else {
                if (Globals.DEBUG_NEX) {
                    System.err.println("Heuristic: Decided to only use" + " Backward Narrowing");
                }
                log.info("Heuristic: Decided to only use Backward" + " Narrowing");
            }
        }
    }

    @Override
    public boolean forwardNarrowing() {
        return this.forwardNarrowing;
    }

    @Override
    public boolean backwardNarrowing() {
        return this.backwardNarrowing;
    }

    @Override
    public boolean allowVarPos() {
        return this.allowVarPos;
    }

    public void increaseDepth() {
        this.narrowingDepth++;
    }

    public boolean passedNarrowingLimits() {
        return false;
    }

    @Override
    public int maximumIterations() {
        return -1;
    }

    @Override
    public int narrowingSteps() {
        return -1;
    }
}
