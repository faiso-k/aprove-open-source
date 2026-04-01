package aprove.verification.complexity.CpxTrsProblem.Processors;

import java.util.*;
import java.util.Map.*;

import aprove.*;
import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class CpxTrsNonTerminationProcessor extends RuntimeComplexityTrsProcessor {

    private final static ComplexityYNM infty = ComplexityYNM.create(ComplexityValue.infinite(), ComplexityValue.infinite());

    @Override
    protected boolean isRuntimeComplexityTrsApplicable(final RuntimeComplexityTrsProblem obl) {
        return true && Options.certifier == Certifier.NONE;
    }

    @Override
    public Result processRuntimeComplexityTrs(final RuntimeComplexityTrsProblem cpxTrs, final Abortion aborter) throws AbortionException {

        final Loop loop = this.getBasicTermLoop(cpxTrs, aborter);

        if (loop == null) {
            return ResultFactory.unsuccessful();
        }

        return ResultFactory.provedWithValue(CpxTrsNonTerminationProcessor.infty, new CpxTrsLoopProof(cpxTrs, loop));
    }

    private Loop getBasicTermLoop(final RuntimeComplexityTrsProblem cpxTrs, final Abortion aborter) throws AbortionException {

        QTRSProblem qtrs = QTRSProblem.create(cpxTrs.getR());
        if (cpxTrs.getRewriteStrategy() != RewriteStrategy.FULL) {
            qtrs = qtrs.createInnermost();
        }

        final LoopFinder loopFinder = new LoopFinder(qtrs, LoopFinder.Heuristic.NORMAL, 3, 3, 3);

        Set<Loop> loops;

        do {
            loops = loopFinder.getLoops(aborter);

            if (loops != null) {
                for (final Loop loop : loops) {
                    if (this.isBasicTermLoop(loop, cpxTrs)) {
                        return loop;
                    }
                }
            }
        } while (loops != null && !loops.isEmpty());

        return null;
    }

    /**
     * Checks that the loop is possible starting from a Basic Term, by checking
     * if any term (corresponding to a LHS, already instantiated with the
     * substitutions) is basic.
     * @param loop
     * @param cpxTrs
     * @return
     */
    private boolean isBasicTermLoop(final Loop loop, final RuntimeComplexityTrsProblem cpxTrs) {
        final ImmutableSet<FunctionSymbol> defSym = cpxTrs.getDefinedSymbols();

        for (final TRSTerm term : loop.getTerms()) {
            // counts the number of defined symbols in the start term.
            int defSymCount = 0;

            for (final Entry<FunctionSymbol, Integer> e : term.getFunctionSymbolCount().entrySet()) {
                if (defSym.contains(e.getKey())) {
                    defSymCount += e.getValue();
                }
            }

            if (Globals.useAssertions) {
                assert defSymCount > 0;
            }

            if (defSymCount == 1) {
                return true;
            }
        }

        return false;
    }

    private class CpxTrsLoopProof extends CpxProof {

        private final RuntimeComplexityTrsProblem cpxTrs;
        private final Loop loop;

        public CpxTrsLoopProof(final RuntimeComplexityTrsProblem cpxTrs, final Loop loop) {
            this.cpxTrs = cpxTrs;
            this.loop = loop;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder retStr = new StringBuilder();

            retStr.append(eu.set(this.cpxTrs.getR(), Export_Util.RULES) + eu.linebreak());

            retStr.append(this.loop.export(eu));

            retStr.append(eu.linebreak() + "Since at least one term in the sequence contains only one "
                + "defined symbol, this loop can be started with a basic term. "
                + "Hence, the TRSs has infinite runtime complexity.");

            return retStr.toString();
        }

    }

}
