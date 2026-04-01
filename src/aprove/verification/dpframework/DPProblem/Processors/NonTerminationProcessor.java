package aprove.verification.dpframework.DPProblem.Processors;

import java.math.*;
import java.util.*;
import java.util.concurrent.atomic.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Processors.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * <p>
 * (debug output: DEBUG_SPECIALMAN)
 * </p>
 * <p>
 * Implementation of a processor that tries to prove nontermination. It checks
 * if there exists a dependency pair <s,t> where s sigma can be narrowed by the
 * given rules to t' and s and t' semiunify.
 * </p>
 * <p>
 * Used heuristic:
 * <ul>
 * <li>If P united with R is rightlinear and not leftlinear we first narrow to
 * the right, otherwise we narrow to the left.</li>
 * <li>If P united with R is not leftlinear we moreover permit narrowing in
 * variables.</li>
 * </ul>
 * </p>
 * <p>
 * Parameters:
 * <ul>
 * <li>if you use negative numbers for all three limits there will be no limit</li>
 * <li>TotalLimit: number of applications of one rule in the narrowing sequences
 * of both directions</li>
 * <li>LeftLimit: number of applications of one rule in the narrowing sequence
 * to the left</li>
 * <li>RightLimit: number of applications of one rule in the narrowing sequence
 * to the right</li>
 * </ul>
 * </p>
 *
 * @author Matthias Sondermann, Rene Thiemann
 * @version $Id$
 */
public class NonTerminationProcessor extends QDPProblemProcessor{

    public static AtomicInteger procNumber = new AtomicInteger(1);

    public static enum Heuristic {
        NORMAL, // standard heuristic which uses backward or forward narrowing and sometimes performs narrowing into variables
        ONLY_FORWARD_NARROWING // only do forward narrowing where narrowing into variables is NOT allowed (sufficient for outermost transformation)
    }

    static enum Direction{
        LEFT, RIGHT, NONE
    }

    public static enum Trs{
        P, R
    }

    static final Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.NonTerminationProcessor");
    /**
     * maximal number of narrowings with one rule
     */
    private final int totalLimit;
    /**
     * maximal number of narrowings to the left with one rule (to be more precise with rule^{-1})
     */
    private final int leftLimit;
    /**
     * maximal number of narrowings to the right with one rule
     */
    private final int rightLimit;
    /**
     * heuristic which controls whether to narrow into variables, which direction first, ...
     */
    private final Heuristic heuristic;
    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        return true;
    }

    /**
     * default application limit is 3
     */
    @ParamsViaArguments({"TotalLimit","LeftLimit","RightLimit","Heuristic"})
    public NonTerminationProcessor(final int totalLimit, final int leftLimit, final int rightLimit, final Heuristic heuristic) {
        this.totalLimit = totalLimit;
        this.leftLimit = leftLimit;
        this.rightLimit = rightLimit;
        this.heuristic = heuristic;
    }

    @Override
    public Result processQDPProblem(final QDPProblem qdpProblem, final Abortion abortion) throws AbortionException{
        // create new procedure and start it
        final NonTerminationProcedure proc = new NonTerminationProcedure(NonTerminationProcessor.procNumber.getAndIncrement(), qdpProblem, this.totalLimit, this.leftLimit, this.rightLimit, this.heuristic);
        return proc.processQDPProblem(abortion);
    }
}