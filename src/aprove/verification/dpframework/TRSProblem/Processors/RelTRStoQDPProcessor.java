package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Checks if the given relative termination problem is root-restricted and
 * nonduplicating. If so, treat it as a DP problem.
 *
 * @author Ulrich Schmidt-Goertz
 */
@NoParams
public class RelTRStoQDPProcessor extends RelTRSProcessor {

    /**
     * A relative termination problem (R, S) is root-restricted if defined
     * symbols from R do not occur on rhs's of S at all, and on rhs's of R
     * only at the root position.
     *
     * @param problem A relative termination problem.
     * @return true iff <code>problem</code> is root-restricted.
     */
    protected static boolean isRootRestricted(final RelTRSProblem problem) {

        final Set<FunctionSymbol> rDef = problem.getDefinedSymbolsOfR();

        final Set<FunctionSymbol> sRhsFSyms = new HashSet<FunctionSymbol>();
        for (final Rule sRule : problem.getS()) {
            final TRSTerm sRhs = sRule.getRight();
            sRhsFSyms.addAll(sRhs.getFunctionSymbols());
        }
        sRhsFSyms.retainAll(rDef);

        final Set<FunctionSymbol> rRhsNonRootSyms = new HashSet<FunctionSymbol>();
        for (final Rule rRule : problem.getR()) {
            final TRSTerm rRhs = rRule.getRight();
            final Collection<Pair<Position, TRSFunctionApplication>> rRhsSubterms =
                rRhs.getNonRootNonVariablePositionsWithSubTerms();
            for (final Pair<Position, TRSFunctionApplication> rRhsSubterm : rRhsSubterms) {
                rRhsNonRootSyms.add(rRhsSubterm.y.getRootSymbol());
            }
        }
        rRhsNonRootSyms.retainAll(rDef);

        return sRhsFSyms.isEmpty() && rRhsNonRootSyms.isEmpty();
    }

    /**
     * A relative termination problem (R, S) is duplicating if there is a rule
     * in either R or S which contains a variable that occurs more often on
     * the rhs than on the lhs.
     * @param problem A relative termination problem.
     * @return true iff <code>problem</code> is duplicating.
     */
    protected static boolean isDuplicating(final RelTRSProblem problem) {

        for (final Rule rule : problem.getR()) {
            if (rule.isDuplicating()) {
                return true;
            }
        }
        for (final Rule rule : problem.getS()) {
            if (rule.isDuplicating()) {
                return true;
            }
        }
        return false;
    }

    @Override
    protected Result processRelTRS(final RelTRSProblem problem, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {

        if (Options.certifier.isCeta() || !RelTRStoQDPProcessor.isRootRestricted(problem) || RelTRStoQDPProcessor.isDuplicating(problem)) {
            return ResultFactory.notApplicable();
        }
        final QTRSProblem rWithQ = QTRSProblem.create(problem.getS());
        final QDPProblem newQDP = QDPProblem.create(problem.getR(), rWithQ, false);
        return ResultFactory.proved(newQDP, YNMImplication.SOUND, new RelTRStoQDPProof());
    }

    public static class RelTRStoQDPProof extends RelTRSProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "The relative termination problem is root-restricted. We can therefore treat it as a dependency pair problem.";
        }

    }
}
