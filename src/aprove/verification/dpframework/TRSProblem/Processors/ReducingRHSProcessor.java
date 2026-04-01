package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

@NoParams
public class ReducingRHSProcessor extends QTRSProcessor {

    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        return qtrs.getQ().isEmpty();
    }

    @Override
    protected Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        if (Globals.useAssertions) {
            assert(this.isApplicable(qtrs));
        }
        final Set<Rule> R = qtrs.getR();
        final ReduceRHSChecker rc = new ReduceRHSChecker(R);
        final Map<Position,Set<Pair<Rule,TRSTerm>>> pos2rules = new LinkedHashMap<Position,Set<Pair<Rule,TRSTerm>>>();
        final Map<Rule,Rule> rewritten = new LinkedHashMap<Rule,Rule>();
outerLoop:
        for (final Rule rule : R) {
            pos2rules.clear();
            rc.collectRewritablePositionsAndRules(rule, pos2rules);
            for (final Map.Entry<Position, Set<Pair<Rule,TRSTerm>>> entry : pos2rules.entrySet()) {
                for (final Pair<Rule,TRSTerm> candidate : entry.getValue()) {
                    final Rule candidateRule = candidate.x;
                    final TRSFunctionApplication left = candidateRule.getLeft();
                    if (left.isLinear() && candidateRule.isNonErasing() && rc.doesNotOverlap(candidateRule)) {
                        final Rule newRule = Rule.create(rule.getLeft(), candidate.y);
                        if (!rule.equals(newRule)) {
                            rewritten.put(rule, newRule);
                            break outerLoop;
                        }
                    }
                }
            }
        }
        if (rewritten.isEmpty()) {
            return ResultFactory.unsuccessful();
        }
        final Set<Rule> newR = new LinkedHashSet<Rule>(R);
        newR.removeAll(rewritten.keySet());
        newR.addAll(rewritten.values());
        final QTRSProblem newQtrs = QTRSProblem.create(ImmutableCreator.create(newR));
        final Implication direction = YNMImplication.EQUIVALENT;
        final Proof proof = new ReducingRHSProof(qtrs, newQtrs, rewritten);
        return ResultFactory.proved(newQtrs, direction, proof);
    }

    private static class ReducingRHSProof extends QTRSProof {

        private final Map<Rule, Rule> rewritten;
        private final QTRSProblem origTrs, resultTrs;

        private ReducingRHSProof(final QTRSProblem origTrs, final QTRSProblem resultTrs, final Map<Rule, Rule> rewritten)
        {
            this.rewritten = rewritten;
            this.origTrs = origTrs;
            this.resultTrs = resultTrs;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("Rewrote reducable right-hand side"+ o.cite(Citation.REDRHS)+":");
            sb.append(o.linebreak());
            for (final Map.Entry<Rule,Rule> entry : this.rewritten.entrySet()) {
                sb.append(entry.getKey().toString());
                sb.append(o.implication());
                sb.append(entry.getValue().toString());
                sb.append(o.linebreak());
            }
            return sb.toString();
        }

    }

}