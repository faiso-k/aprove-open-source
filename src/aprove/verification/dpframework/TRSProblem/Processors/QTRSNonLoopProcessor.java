package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.nontermination.*;

/**
 * This processor is the implementation of the Bachelor thesis:<br>
 * <b>"Detecting Non-Termination of Non-Looping Term Rewrite Systems"</b><br>
 * by Tim Enger
 *
 * @author Tim Enger
 */

public class QTRSNonLoopProcessor extends QTRSProcessor {
    // TODO this class looks broken atm. The variable nonLoop below is always null

    /** settings **/
    // also make use of backward narrowing
    private final boolean BACKWARD_NARROWING;

    // Narrowing into variable positions?
    private final boolean ALLOW_VARPOS;

    @ParamsViaArgumentObject
    public QTRSNonLoopProcessor(final Arguments args) {
        this.BACKWARD_NARROWING = args.BACKWARD_NARROWING;
        this.ALLOW_VARPOS = args.ALLOW_VARPOS;
    }

    @Override
    public boolean isQTRSApplicable(QTRSProblem qtrs) {
        return true;
    }

    @Override
    protected Result processQTRS(QTRSProblem qtrs,
        Abortion aborter,
        RuntimeInformation rti) throws AbortionException {

        if (Globals.DEBUG_NEX) {
            System.err.println("QTRS NonLoop started");
        }

        // the (Pattern-) Rules created in n-2
        Set<PatternRule> pRules = new HashSet<PatternRule>();

        // transform every Rule to a ProofedRule

        NonLoopProof nonLoop = null;

        // the (Pattern-) Rules created in n-1
        Set<PatternRule> newPRules = new HashSet<PatternRule>();

        // the (Pattern-) Rules created in n
        // by combinating the (Pattern-) Rules from n-1 and n-2
        Set<PatternRule> createdPRules = new HashSet<PatternRule>();

        while (nonLoop == null) {

            aborter.checkAbortion();

            /** PATTERN CREATION I & II & III **/
            // try to find new PatternRules

            /** NARROWING **/
            // narrow old rules with new rules and vice versa

            /** BACKWARD NARROWING **/
            if (this.BACKWARD_NARROWING) {
            }

            /** check for nonlooping PatternRule **/
            for (PatternRule pRule : createdPRules) {
                if (true) {
                    nonLoop = null;
                    break;
                }
            }

            // if there are no newly created rules we can abort
            // since we can't show non-termination
            if (createdPRules.isEmpty()) {
                return ResultFactory.aborted("Cannot show Non-Termination");
            }

            pRules.addAll(newPRules);

            newPRules = new HashSet<PatternRule>(createdPRules);

            createdPRules = new HashSet<PatternRule>();
        }

        return ResultFactory.disproved(nonLoop);
    }

    public static class Arguments {
        public boolean BACKWARD_NARROWING = false;
        public boolean ALLOW_VARPOS = false;
    }
}
