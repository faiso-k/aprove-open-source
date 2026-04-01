package aprove.verification.complexity.CdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Convert (D, S, K, R) to a relative TRS where S are the standard rules,
 * and D \ S as well as R are the relative rules.
 * 
 * @author Carsten Fuhs
 */
public class CdtToCpxRelTrsProcessor extends CdtProblemProcessor {

    private static final Proof THE_PROOF = new CdtToCpxRelTrsProof();

    @Override
    protected boolean isCdtApplicable(CdtProblem obl) {
        // the technique is currently not supported by any certifier
        return Options.certifier.isNone();
    }

    @Override
    protected Result processCdt(CdtProblem cdtProblem, Abortion aborter) throws AbortionException {
        CpxRelTrsProblem newObl = toRelTrs(cdtProblem);
        // Lower bound sound as well due to the shape of CDT problems.
        Result res = ResultFactory.proved(newObl, BothBounds.create(), THE_PROOF);
        return res;
    }

    /**
     * Converts (D, S, K, R) to S as standard rules and (D \setminus S) \cup R
     * as relative rules.
     *
     * @param cdtProblem (D, S, K, R); non-null
     * @return S as standard rules and (D \setminus S) \cup R as relative rules
     */
    private static CpxRelTrsProblem toRelTrs(CdtProblem cdtProblem) {
        ImmutableSet<Cdt> oldS = cdtProblem.getS();
        ImmutableSet<Cdt> oldTuples = cdtProblem.getTuples();
        Set<Rule> oldR = cdtProblem.getR();

        Set<Rule> newR = new LinkedHashSet<>();
        Set<Rule> newS = new LinkedHashSet<>();

        // generate the standard rules...
        for (Cdt cdt : oldS) {
            newR.add(cdt.getRule());
        }

        // ... then the relative rules
        for (Cdt cdt : oldTuples) {
            if (! oldS.contains(cdt)) {
                newS.add(cdt.getRule());
            }
        }
        for (Rule rule : oldR) {
            newS.add(rule);
        }

        CpxRelTrsProblem res = RuntimeComplexityRelTrsProblem.create(ImmutableCreator.create(newR),
                ImmutableCreator.create(newS), RewriteStrategy.INNERMOST, false);
        return res;
    }

    private static class CdtToCpxRelTrsProof extends CpxProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("Converted S to standard rules, and D \\ S as well as R to relative rules.");
        }
    }
}
