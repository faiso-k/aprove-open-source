package aprove.verification.dpframework.Utility.NonLoop.NonLoopSearch.heuristics;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.equivalence.*;

/**
 * @author Tim Enger
 */

public class NarrowingHeuristic {

    public enum NarrowingDirection {
        Forward, Backward, OnlyRoot
    }

    public static Set<ProofedRule> narrowing(final ProofedRule lr, final ProofedRule st) {
        return NarrowingHeuristic.narrowing(lr, st, NarrowingDirection.Forward);
    }

    public static Set<ProofedRule> narrowing(ProofedRule lr, ProofedRule st, final NarrowingDirection dir) {
        final Set<ProofedRule> rv = new LinkedHashSet<ProofedRule>();

        // TODO the following fresh renaming should not be necessary on both
        // sides. it is only included here because currently domain variables
        // occur in the instantiated terms
        lr = lr.getStandardLeft();
        st = st.getStandardRight();
        if (Globals.useAssertions) {
            final Set<TRSVariable> lrVars = lr.getPatternRule().getAllVariables();
            final Set<TRSVariable> stVars = st.getPatternRule().getAllVariables();
            lrVars.retainAll(stVars);
            final Set<TRSVariable> lDVars = lr.getPatternRule().getLhs().getDomainVariables();
            final Set<TRSVariable> rDVars = lr.getPatternRule().getRhs().getDomainVariables();
            final Set<TRSVariable> sDVars = st.getPatternRule().getLhs().getDomainVariables();
            final Set<TRSVariable> tDVars = st.getPatternRule().getRhs().getDomainVariables();
            final LinkedHashSet<TRSVariable> allDomVars = new LinkedHashSet<>();
            allDomVars.addAll(lDVars);
            allDomVars.addAll(rDVars);
            allDomVars.addAll(sDVars);
            allDomVars.addAll(tDVars);
            for (final TRSVariable x : allDomVars) {
                int count = 0;
                count += lDVars.contains(x) ? 1 : 0;
                count += rDVars.contains(x) ? 1 : 0;
                count += sDVars.contains(x) ? 1 : 0;
                count += tDVars.contains(x) ? 1 : 0;
                assert count == 1;
            }
            assert lrVars.isEmpty();
        }

        final Set<Position> positions = new LinkedHashSet<>();
        switch (dir) {
        case Forward:
            positions.addAll(Utils.getNonVarPos(lr.getPatternRule().getRhs().getT()));
            break;
        case Backward:
            positions.addAll(Utils.getNonVarPos(st.getPatternRule().getLhs().getT()));
            break;
        case OnlyRoot:
            positions.add(Position.create());
            break;
        }
        for (final Position pi : positions) {
            ProofedRule pr = NarrowingState.narrow(lr, st, pi, dir);
            if (pr != null) {
                // System.err.println("NH: " + pr);
                pr = Equivalence.createRemoveAllIrrelevant(pr);
                pr = SimplifyMuHeuristic.simplifyMu(pr);
                rv.add(pr);
            }
        }
        return rv;
    }

    public static Set<ProofedRule> backwardNarrowing(final ProofedRule lr, final ProofedRule st) {
        return NarrowingHeuristic.narrowing(lr, st, NarrowingDirection.Backward);
    }
}
