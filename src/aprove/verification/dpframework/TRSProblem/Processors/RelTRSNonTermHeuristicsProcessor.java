package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Some simple heuristics for relative non-termination,
 * from Geser's PhD thesis.
 * @author Ulrich Schmidt-Goertz
 */
@NoParams
public class RelTRSNonTermHeuristicsProcessor extends RelTRSProcessor {

    @Override
    public Result processRelTRS(final RelTRSProblem problem, final Abortion aborter, final RuntimeInformation rti)
            throws AbortionException {

        boolean rHasRhsVariable = false;
        for (final Rule rule : problem.getR()) {
            if (RelTRSNonTermHeuristicsProcessor.hasRhsVariable(rule)) {
                rHasRhsVariable = true;
            }
        }

        Proof proof = null;
        for (final Rule rule : problem.getS()) {
            if (rHasRhsVariable && RelTRSNonTermHeuristicsProcessor.ruleIsLeftErasing(rule)) {
                proof = RelTRSNonTermHeuristicProof.createLeftErasingProof(problem, rule);
                break;
            }
            if (rHasRhsVariable && RelTRSNonTermHeuristicsProcessor.ruleIsRightDuplicating(rule)) {
                proof = RelTRSNonTermHeuristicProof.createRightDuplicatingProof(problem, rule);
                break;
            }
        }
        if (proof != null) {
            return ResultFactory.disproved(proof);
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    private static boolean hasRhsVariable(final Rule rule) {
        return rule.getRight().getVariables().size() > 0;
    }

    /**
     * A rule is left-erasing if it has variables on the right-hand side
     * that do not appear on the left-hand side.
     * @param rule A rewrite rule.
     * @return true iff the rule is left-erasing.
     */
    private static boolean ruleIsLeftErasing(final Rule rule) {

        final Set<TRSVariable> leftVars = rule.getLeft().getVariables();
        final Set<TRSVariable> rightVars = rule.getRight().getVariables();
        return !leftVars.containsAll(rightVars);
    }

    /**
     * A rule is right-duplicating if it is of the form x -> r and x occurs
     * more than once in r.
     * @param rule A rewrite rule.
     * @return true iff the rule is right-duplicating.
     */
    private static boolean ruleIsRightDuplicating(final Rule rule) {
        // Note: Since lhs's of rules can *never* be variables in AProVE,
        return false;
    }

    public static class RelTRSNonTermHeuristicProof extends Proof.DefaultProof {

        private RelTRSProblem problem;
        private Rule leftErasingRule = null;
        private Rule rightDuplicatingRule = null;

        /**
         * Create a non-termination proof based on the fact that S contains
         * a left-erasing rule.
         * @param problem The problem whose non-termination is proved.
         * @param witness The left-erasing rule.
         * @return The proof object.
         */
        public static RelTRSNonTermHeuristicProof createLeftErasingProof(final RelTRSProblem problem, final Rule witness) {

            final RelTRSNonTermHeuristicProof proof = new RelTRSNonTermHeuristicProof();
            proof.problem = problem;
            proof.leftErasingRule = witness;
            return proof;
        }

        /**
         * Create a non-termination proof based on the fact that S contains
         * a right-duplicating rule.
         * @param problem The problem whose non-termination is proved.
         * @param witness The right-duplicating rule.
         * @return The proof object.
         */
        public static RelTRSNonTermHeuristicProof createRightDuplicatingProof(final RelTRSProblem problem,
            final Rule witness) {

            final RelTRSNonTermHeuristicProof proof = new RelTRSNonTermHeuristicProof();
            proof.problem = problem;
            proof.rightDuplicatingRule = witness;
            return proof;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {

            StringBuilder result;
            result = new StringBuilder();
            final Citation citation = Citation.GESER;
            result.append("The following relative termination problem is given:");
            result.append(o.linebreak());
            result.append(this.problem.export(o));
            result.append(o.linebreak());
            if (this.leftErasingRule != null) {
                result.append("The following rule from S is left-erasing:");
                result.append(o.linebreak());
                result.append(this.leftErasingRule.export(o));
            } else if (this.rightDuplicatingRule != null) {
                result.append("The following rule from S is right-duplicating:");
                result.append(o.linebreak());
                result.append(this.rightDuplicatingRule.export(o));
            } else {
                assert (false) : "No proof reason given";
            }
            result.append(o.linebreak());
            result.append("By " + o.cite(citation) + ", R/S does not terminate.");
            return result.toString();
        }
    }
}
