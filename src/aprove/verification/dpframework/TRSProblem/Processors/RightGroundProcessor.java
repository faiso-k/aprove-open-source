package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Processor which decides termination for right-ground TRSs
 */
@NoParams
public class RightGroundProcessor extends QTRSProcessor {

    private final static Logger log = Logger.getLogger("aprove.verification.dpframework.TRSProblem.Processors.RightGroundProcessor");

    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        return qtrs.isRightGround();
    }

    @Override
    protected Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        final Set<Rule> R = qtrs.getR();
        final QTermSet Q = qtrs.getQ();
        final Map<FunctionSymbol, ImmutableSet<Rule>> ruleMap = qtrs.getRuleMap();
        TRSTerm badRhs = null;
        TRSTerm badResult = null;
        final int n = R.size();
        final TRSTerm[] rhs = new TRSTerm[n];
        final Set<TRSTerm>[] terms = new Set[n];
        int i = 0;
        for (final Rule rule : R) {
            rhs[i] = rule.getRight();
            terms[i] = new LinkedHashSet<TRSTerm>();
            terms[i].add(rhs[i]);
            if (RightGroundProcessor.log.isLoggable(Level.FINEST)) {
                RightGroundProcessor.log.log(Level.FINEST, "T"+i+" = "+terms[i]+"\n");
            }
            if (Globals.useAssertions) {
                assert(rhs[i].getVariables().isEmpty());
            }
            i++;
        }
        while (badRhs == null) {
            aborter.checkAbortion();
            if (RightGroundProcessor.log.isLoggable(Level.FINEST)) {
                RightGroundProcessor.log.log(Level.FINEST, "--------------------------------------\n");
            }
            int empties = 0;
            for (i = 0; i < n; i++) {
                if (terms[i].isEmpty()) {
                    empties++;
                    continue;
                }
                final Set<TRSTerm> newTerms = new LinkedHashSet<TRSTerm>();
                for (final TRSTerm term : terms[i]) {
                    newTerms.addAll(RightGroundProcessor.allRewritings(term, ruleMap, Q, aborter));
                }
                terms[i] = newTerms;
                if (RightGroundProcessor.log.isLoggable(Level.FINEST)) {
                    RightGroundProcessor.log.log(Level.FINEST, "T"+i+" = "+terms[i]+"\n");
                }
                badResult = RightGroundProcessor.containsRhs(newTerms, rhs[i]);
                if (badResult != null) {
                    // non-termination!
                    badRhs = rhs[i];
                    if (RightGroundProcessor.log.isLoggable(Level.FINE)) {
                        RightGroundProcessor.log.log(Level.FINE, "T"+i+" contains "+badResult+" which has "+badRhs+" as a subterm!\n");
                    }
                    break;
                }
            }
            if (empties == n) {
                // termination!
                if (RightGroundProcessor.log.isLoggable(Level.FINE)) {
                    RightGroundProcessor.log.log(Level.FINE, "All Ti are empty!\n");
                }
                break;
            }
        }
        final Proof proof = new RightGroundProof(qtrs, badRhs, badResult);
        return badRhs == null ? ResultFactory.proved(proof) : ResultFactory.disproved(proof);
    }

    private static TRSTerm containsRhs(final Set<TRSTerm> terms, final TRSTerm rhs) {
        for (final TRSTerm term : terms) {
            if (term.getSubTerms().contains(rhs)) {
                return term;
            }
        }
        return null;
    }

    /**
     * Generates all possible rewritings for the given term regarding R restricted by Q
     */
    private static Set<TRSTerm> allRewritings(final TRSTerm term, final Map<FunctionSymbol, ImmutableSet<Rule>> ruleMap, final QTermSet Q, final Abortion aborter) throws AbortionException {
        final Set<TRSVariable> termVars = term.getVariables();
        final Set<TRSTerm> newTerms = new LinkedHashSet<TRSTerm>();
        // iterate over all subterms of term
        for(final Pair<Position,TRSTerm> actPosTermPair : term.getPositionsWithSubTerms()) {

            // check every trs rule at every (non variable) position
            final Position actPos = actPosTermPair.x;
            final TRSTerm actSubterm = actPosTermPair.y;

            // now check every rule for rewriting with a useful root symbol
            final FunctionSymbol fs = ((TRSFunctionApplication) actSubterm).getRootSymbol();
            final ImmutableSet<Rule> actRules = ruleMap.get(fs);
            if (actRules == null) {
                // no rules, i.e., fs is a constructor
                continue;
            }

            YNM canBeRewritten = YNM.MAYBE;
            for (Rule actRule : actRules) {
                aborter.checkAbortion();
                //  variables of rule and subterm have to be disjoint
                actRule = actRule.renameVariables(termVars);

                final TRSTerm l = actRule.getLeft();
                final TRSTerm r = actRule.getRight();

                // try to unify term.subTerm and actual rule
                final TRSSubstitution actMatcher = l.getMatcher(actSubterm);
                if (actMatcher != null) {
                    // possible rewriting found so do it!
                    // do we have to forbid that because of Q?

                    // check if every non variable subterm is Q-normal
                    if (canBeRewritten == YNM.MAYBE) {
                        canBeRewritten = YNM.fromBool(Q.canBeRewrittenBelowRoot(actSubterm));
                    }
                    if (canBeRewritten.toBool()) {
                        // there is a proper subterm that is not Q-normal
                        break;
                    }
                    final TRSTerm newTerm = term.replaceAt(actPos,r.applySubstitution(actMatcher));
                    newTerms.add(newTerm);
                }
            }
        }
        return newTerms;
    }

    private static class RightGroundProof extends QTRSProof {

        private final TRSTerm rhs;
        private final TRSTerm result;
        private final QTRSProblem origTrs;

        public RightGroundProof(final QTRSProblem origTrs, final TRSTerm rhs, final TRSTerm result) {
            this.origTrs = origTrs;
            this.rhs = rhs;
            this.result = result;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            if (this.rhs == null) {
                return eu.export("The TRS is right-ground and all right-hand sides can only be evaluated finitely often. Thus, the TRS is terminating "+ eu.cite(Citation.RIGHTGROUND)+".");
            } else {
                return eu.export("The term "+this.rhs+" can be rewritten to "+this.result+". Thus, the TRS is not terminating.");
            }
        }

    }
}
