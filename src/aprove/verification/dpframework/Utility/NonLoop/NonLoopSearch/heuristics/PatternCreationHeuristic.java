package aprove.verification.dpframework.Utility.NonLoop.NonLoopSearch.heuristics;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.creation.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.equivalence.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Tim Enger
 */

public abstract class PatternCreationHeuristic {

    public static Set<ProofedRule> findPatterns(final ProofedRule rule) {

        final Set<ProofedRule> result = new LinkedHashSet<ProofedRule>();

        if (!rule.getPatternRule().isSigmaAndMuEmpty()) {
            return result;
        }

        final PatternRule pRule = rule.getPatternRule();
        final PatternTerm lhs = pRule.getLhs();
        final PatternTerm rhs = pRule.getRhs();

        final TRSTerm l = lhs.getT();
        final TRSTerm r = rhs.getT();

        /*** PATTERN CREATION I : l\theta = r\sigma ***/
        Pair<TRSSubstitution, TRSSubstitution> subs = Utils.findSubstitutions(l, r);

        if (subs != null && Utils.commutative(subs.x, subs.y)) {
            final ProofedRule res = PatternCreationI.create(rule, TRSSubstitution.create(), subs.x, subs.y);
            result.add(Equivalence.createRemoveAllIrrelevant(res));
        }

        /*** PATTERN CREATION I : l\delta = r\delta\sigma ***/
        subs = r.getSemiSubstitutions(l);

        if (subs != null) {
            final ProofedRule res = PatternCreationI.create(rule, subs.y, TRSSubstitution.create(), subs.x);
            result.add(Equivalence.createRemoveAllIrrelevant(res));
        }

        /*** PATTERN CREATION II : l = r|_\pi\sigma ***/
        // for every non-variable position in r
        for (final Position pi : Utils.getNonVarPos(r)) {
            // we decided that we should exclude the root position in the
            // implementation, otherwise rule like
            // isNat(s(x))[x / s(x)]^n[ ] -> z[x / s(x)]^n[z / isNat(x)]
            // would be created
            if (pi.isEmptyPosition()) {
                continue;
            }
            final TRSTerm rsub = r.getSubterm(pi);

            final TRSSubstitution sigma = rsub.getMatcher(l);

            if (sigma != null) {
                final ProofedRule res = PatternCreationII.create(rule, pi, sigma);
                result.add(Equivalence.createRemoveAllIrrelevant(res));
            }
        }

        return result;
    }
}
