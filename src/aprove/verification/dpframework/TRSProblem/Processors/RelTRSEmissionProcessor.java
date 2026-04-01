package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This processor tries to determine whether the TRS S is "emitting"
 * R-redexes, in which case it is non-terminating.
 * For the theory see my diploma thesis.
 * @author Ulrich Schmidt-Goertz
 */
@NoParams
public class RelTRSEmissionProcessor extends RelTRSProcessor {

    /**
     * The sequence s ->* t is an R-emitting loop if R is non-empty and t = C[s\sigma,u] and
     * either the subterm u contains an R-redex or
     * NOT SOUND AND DEACTIVATED: u contains a variable occurring in s\sigma.
     * NEW version (by Rene Thiemann): u contains a variable x where x also occurs in \sigma(x).
     * Proof for new version:
     *   let l -> r be any rule of R.
     *   Then s sigma^n {x/l} ->^* C'[ s sigma^n+1 {x/l}, u sigma^n {x/l}] -l->r-> C'[ s sigma^n+1 {x/l}, v]
     *     where v is obtained as follows: u = D[x], hence u sigma^n {x/l} = D'[ x sigma^n {x/l}] must contain l,
     *     and thus can be rewritten to some term v by rule l->r.
     *   Clearly, the sequence can be extended infinitely by increasing n and stacking more and more contexts C'[Hole, v],
     *   i.e., s {x/l} = s sigma^0 {x/l} is a non-terminating term.
     * @param s A term.
     * @param t Another term.
     * @param problem The relative termination problem R/S.
     * @return true iff s ->* t is R-emitting.
     */
    private static boolean isEmitting(
            final TRSTerm s,
            final TRSTerm t,
            final RelTRSProblem problem) {

        final Collection<Pair<Position, TRSTerm>> tSubterms = t.getPositionsWithSubTerms();

        // first find out whether t contains an instance of s
        for (Pair<Position, TRSTerm> sInstance : tSubterms) {
            if (sInstance.x.isEmptyPosition()) {
                continue;
            }
            TRSSubstitution sigma = s.getMatcher(sInstance.y);
            if (sigma != null) {
                // ok, now check all subterms that lie orthogonal to sInstance for
                // whether they are a variable from s or can be rewritten with R
                for (Pair<Position, TRSTerm> redex : tSubterms) {
                   if (!redex.x.isIndependent(sInstance.x)) {
                       continue;
                   }
                   final TRSTerm subterm = redex.y;
                   if (subterm.isVariable()) {
                       TRSVariable x = (TRSVariable) subterm;
                       if (sigma.substitute(x).getVariables().contains(x)) {
                           return true;
                       }
                   } else {
                       Set<TRSTerm> rewritings = subterm.rewrite(Rule.getRuleMap(problem.getR()));
                       if (!rewritings.isEmpty()) {
                           return true;
                       }
                   }
                } // inner for-loop
            }
        } // outer for-loop
        return false;
    }

    /**
     * Try to find an R-emitting S-loop.
     * @param problem A relativbe termination problem R/S
     * @return A list of terms that form an R-emitting S-loop,
     * or null if no such loop could be found.
     */
    private static List<TRSTerm> findEmittingSequence(final RelTRSProblem problem) {

        for (Rule sRule : problem.getS()) {
            final List<TRSTerm> result = RelTRSEmissionProcessor.findEmittingSequence(sRule.getLeft(), sRule.getLeft(), problem, 1);
            if (result != null) {
                Collections.reverse(result);
                return result;
            }
        }
        return null;
    }

    /**
     * Check if startTerm ->* currentTerm is a prefix of an R-emitting
     * S-loop of length at most |S|.
     * @param startTerm The start term of the wanted loop.
     * @param currentTerm The term up to which we already have gone.
     * @param problem The relative termination problem R/S.
     * @param depth The length of the sequence startTerm ->* currentTerm.
     * @return
     */
    private static List<TRSTerm> findEmittingSequence(
            final TRSTerm startTerm,
            final TRSTerm currentTerm,
            final RelTRSProblem problem,
            final int depth) {

        final Set<Rule> sRules = problem.getS();
        if (RelTRSEmissionProcessor.isEmitting(startTerm, currentTerm, problem)) {
            final List<TRSTerm> result = new ArrayList<TRSTerm>();
            result.add(currentTerm);
            return result;
        } else if (depth <= sRules.size()){
            final Set<TRSTerm> rewritings = currentTerm.rewrite(Rule.getRuleMap(sRules));
            for (TRSTerm rewriting : rewritings) {
                final List<TRSTerm> result = RelTRSEmissionProcessor.findEmittingSequence(startTerm, rewriting, problem, depth+1);
                if (result != null) {
                    result.add(currentTerm);
                    return result;
                }
            }
        }
        return null;
    }

    @Override
    public boolean isRelTRSApplicable(final RelTRSProblem qtrs) {
        return !qtrs.getR().isEmpty() && !(Options.certifier.isCeta() || Options.certifier.isCpf());
    }


    @Override
    protected Result processRelTRS(
            final RelTRSProblem problem,
            final Abortion aborter,
            final RuntimeInformation rti) throws AbortionException {

        final List<TRSTerm> result = RelTRSEmissionProcessor.findEmittingSequence(problem);
        if (result != null) {
            final Proof proof = new RelTRSEmissionProof(result);
            return ResultFactory.disproved(proof);
        } else {
            return ResultFactory.unsuccessful();
        }
    }


    public static class RelTRSEmissionProof extends RelTRSProof {

        private final List<TRSTerm> sequence;

        public RelTRSEmissionProof(final List<TRSTerm> sequence) {
            this.sequence = sequence;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {

            StringBuilder sb = new StringBuilder("The TRS S admits the following R-emitting loop:");
            sb.append(o.linebreak());
            for (int i = 0; i < this.sequence.size(); i++) {
                sb.append(this.sequence.get(i).export(o));
                if (i < this.sequence.size() - 1) {
                    sb.append(o.rightarrow());
                }
            }
            sb.append(o.linebreak());
            sb.append("Therefore R/S does not terminate.");
            return sb.toString();
        }


    }
}
