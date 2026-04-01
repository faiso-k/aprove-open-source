package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

/**
 * Searches for context-sensitive loops by looking for normal loops and checking
 * if they respect the replacement map. Only works for full context-sensitive
 * rewriting. Extension to innermost context-sensitive rewriting possible by
 * creating corresponding matching problems. Based on
 * {@link Citation#THIEMANN_LOOPS_UNDER_STRATEGIES}.
 * @see OTRSNonTerminationProcessor
 */
@NoParams
public class CSRNonTerminationProcessor extends CSRProcessor {

    @Override
    public boolean isCSRApplicable(final CSRProblem csr) {
        return !csr.getInnermost(); // for now only supports full CS rewriting
    }

    @Override
    protected Result processCSR(final CSRProblem csr, final Abortion aborter)
            throws AbortionException {

        final Loop loop =
            CSRNonTerminationProcessor.getContextSensitiveLoop(csr, aborter);

        if (loop == null) {
            return ResultFactory.unsuccessful();
        }

        return ResultFactory.disproved(new ContextSensitiveLoopProof(csr, loop));
    }

    private static Loop getContextSensitiveLoop(final CSRProblem csr, final Abortion aborter)
            throws AbortionException {
        final LoopFinder loopFinder =
            new LoopFinder(csr.getR(), LoopFinder.Heuristic.NORMAL, 3, 3, 3);

        Set<Loop> loops;

        do {
            loops = loopFinder.getLoops(aborter);

            if (loops != null) {
                for (final Loop loop : loops) {
                    if (CSRNonTerminationProcessor.isContextsensitiveLoop(loop, csr)) {
                        return loop;
                    }
                }
            }
        } while (loops != null && !loops.isEmpty());
        return null;
    }

    /**
     * By [{@link Citation#THIEMANN_LOOPS_UNDER_STRATEGIES}, Theorem 1] a loop
     * is context-sensitive, iff the derivation from t to C[t\mu] respects the
     * context-sensitive strategy and the hole in C is at a replacing position.
     * @param loop
     * @param csr
     * @return
     */
    private static boolean isContextsensitiveLoop(final Loop loop,
            final CSRProblem csr) {
        final ReplacementMap rm =
            ReplacementMap.create(csr.getReplacementMap());

        /* check that loop respects context-sensitive strategy */
        final ArrayList<Position> positions = loop.getPositions();
        final ArrayList<TRSTerm> terms = loop.getTerms();

        final int l = positions.size();
        for (int i = 0; i < l; ++i) {
            final Position p = positions.get(i);
            final TRSTerm t = terms.get(i);
            if (!rm.isReplacing(t, p)) {
                return false;
            }
        }

        final Context c = loop.getContext();
        if (!rm.isReplacingContext(c)) {
            return false;
        }

        return true;
    }

    private class ContextSensitiveLoopProof extends CSRProof {

        private final CSRProblem csr;
        private final Loop loop;

        public ContextSensitiveLoopProof(final CSRProblem csr, final Loop loop) {
            this.csr = csr;
            this.loop = loop;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder retStr = new StringBuilder();

            retStr.append(eu.set(this.csr.getR(), Export_Util.RULES)
                + eu.linebreak());

            retStr.append(this.loop.export(eu));

            retStr.append(eu.linebreak()
                + "We used ["
                + eu.cite(Citation.THIEMANN_LOOPS_UNDER_STRATEGIES)
                + ", Theorem 1] to show that this loop is an context-sensitive loop.");

            return retStr.toString();
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            return CPFTag.TRS_NONTERMINATION_PROOF
                .create(doc, this.loop.toCPF(doc, xmlMetaData, this.csr.getR(), null));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return !modus.isPositive();
        }

    }
}
