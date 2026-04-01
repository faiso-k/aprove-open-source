package aprove.verification.oldframework.IRSwT.Processors.TraceTermination;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IRSwT.Digraph.*;
import aprove.verification.oldframework.IRSwT.Filters.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Enumerates all traces and decides whether or not there is a trace with relatively terminating rules.
 * @author Matthias Hoelzel
 */
public class TraceProcessor extends Processor.ProcessorSkeleton {
    /** Constructor! */
    public TraceProcessor() {
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return (obl != null && obl instanceof IRSwTProblem && !((IRSwTProblem) obl).isBounded());
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert obl instanceof IRSwTProblem : "Wrong obligation type!";
        final IRSwTProblem irswt = (IRSwTProblem) obl;

        final FreshNameGenerator fng = irswt.createFreshNameGenerator();

        final SortAnalyzer sa = new SortAnalyzer(irswt.getRules());
        final SortDictionary sd = sa.analyze();
        final RemoveIntFilter rif = new RemoveIntFilter(irswt.getRules(), sd, fng);
        final LinkedHashSet<IGeneralizedRule> filteredRules = rif.applyFilter();

        final TraceChecker tc = new TraceChecker(filteredRules, fng, aborter);
        final LinkedHashSet<IGeneralizedRule> result = tc.followTraces();

        if (result == null) {
            return ResultFactory.unsuccessful();
        } else {
            final TraceProof proof = new TraceProof(tc.getTraceOfSuccess(), tc.getRelativelyNonTerminatingTraceRules());

            final LinkedHashSet<IGeneralizedRule> rulesOfNewProblem = rif.getOldRules(result);

            final PartiallyComputedDigraph<IGeneralizedRule> pcd = irswt.getTerminationDigraph();
            final PartiallyComputedDigraph<IGeneralizedRule> newGraph;
            boolean solved = rulesOfNewProblem.isEmpty();
            if (pcd != null) {
                newGraph = pcd.getInducedSubgraph(rulesOfNewProblem);
                newGraph.overestimate();
                if (newGraph.hasOnlyTrivialSCCs()) {
                    solved = true;
                }
            } else {
                newGraph = null;
            }

            if (solved) {
                return ResultFactory.proved(proof);
            }

            final IRSwTProblem newProblem =
                new IRSwTProblem(ImmutableCreator.create(rulesOfNewProblem), newGraph, irswt.getStartTerm());
            final YNMImplication implication =
                irswt.getStartTerm() == null ? YNMImplication.EQUIVALENT : YNMImplication.SOUND;
            return ResultFactory.proved(newProblem, implication, proof);
        }
    }

    /**
     * A truly foolish proof!
     * @author Matthias Hoelzel
     */
    public class TraceProof extends DefaultProof {
        /** The terminating trace we could find. */
        final Trace traceOfSuccess;

        /** Set of relatively non-terminating trace rules. */
        private final LinkedHashSet<IGeneralizedRule> relativelyNonTerminating;

        /** Constructor! */
        public TraceProof(final Trace trace, final LinkedHashSet<IGeneralizedRule> relNonTermRules) {
            this.traceOfSuccess = trace;
            this.relativelyNonTerminating = relNonTermRules;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append(eu.tttext("Investigated the following trace:"));
            sb.append(eu.linebreak());
            this.traceOfSuccess.export(sb, eu);
            sb.append(eu.linebreak());
            sb.append(eu.tttext("The following rules are obviously relatively terminating:"));
            sb.append(eu.linebreak());
            for (final IGeneralizedRule rule : this.traceOfSuccess.getRules()) {
                if (!this.relativelyNonTerminating.contains(rule)) {
                    Trace.exportTraceRule(sb, eu, rule);
                    sb.append(eu.linebreak());
                }
            }
            sb.append(eu.linebreak());
            sb.append(eu.tttext("All other rules are oviously relatively non-terminating!"));
            return sb.toString();
        }
    }
}
