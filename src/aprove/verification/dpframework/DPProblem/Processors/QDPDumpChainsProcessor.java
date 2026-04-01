package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.input.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This processor is used to debug false YESes.
 * @author MP
 */
public class QDPDumpChainsProcessor extends QDPProblemProcessor {

    private final TRSTerm startTerm;
    private final int maxPSteps;
    private final int maxRSteps;

    @ParamsViaArguments(value = { "StartTerm", "MaxRSteps", "MaxPSteps" })
    public QDPDumpChainsProcessor(final String startTerm, final int maxRSteps, final int maxPSteps) {
        this(EasyInput.parseTerm(startTerm), maxRSteps, maxPSteps);
    }

    public QDPDumpChainsProcessor(final TRSTerm startTerm, final int maxRSteps, final int maxPSteps) {
        this.startTerm = startTerm;
        this.maxRSteps = maxRSteps;
        this.maxPSteps = maxPSteps;
    }

    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter)
            throws AbortionException {
        final Map<FunctionSymbol, Set<Rule>> rRuleMap = Rule.getRuleMap(qdp.getR());
        final Map<FunctionSymbol, Set<Rule>> pRuleMap = Rule.getRuleMap(qdp.getP());
        final QTermSet Q = qdp.getQ();

        final CriticalPairs rCriticalPais = new CriticalPairs(qdp.getR(), rRuleMap);
        final boolean rNonOverlapping = rCriticalPais.isNonOverlapping(aborter);

        Set<TRSTerm> terms = Collections.singleton(this.startTerm);
        int pSteps = 0;
        while(pSteps < this.maxPSteps) {
            final Set<TRSTerm> rReachableTerms = new LinkedHashSet<TRSTerm>();
            final Set<TRSTerm> rFinalTerms = new LinkedHashSet<TRSTerm>();
            for (final TRSTerm t : terms) {
                this.rewriteAsOftenAsPossible(t, rRuleMap, Q, rNonOverlapping, this.maxRSteps, rReachableTerms, rFinalTerms);
            }

            this.dumpTerms(rFinalTerms, this.maxRSteps, "R-Steps");

            final Set<TRSTerm> pReachableTerms = new LinkedHashSet<TRSTerm>();
            for (final TRSTerm t : rFinalTerms) {
                pReachableTerms.addAll(this.rewrite(t, pRuleMap, Q));
            }

            pSteps++;
            if (pReachableTerms.isEmpty()) {
                terms = rFinalTerms;
            } else {
                terms = pReachableTerms;
            }

            this.dumpTerms(terms, pSteps, "P-Steps");

            if (pReachableTerms.isEmpty()) {
                break;
            }
        }

        return ResultFactory.unsuccessful();
    }

    private void dumpTerms(final Set<TRSTerm> terms, final int stepCount, final String stepType) {
        final StringBuilder sb = new StringBuilder();
        sb.append("Reachable terms from term " + this.startTerm + " within " + stepCount + " " + stepType + ":\n");
        for (final TRSTerm t : terms) {
            sb.append(t.toString());
            sb.append("\n");
        }
        sb.append("\n");

        System.err.println(sb.toString());
    }

    private void rewriteAsOftenAsPossible(final TRSTerm t, final Map<FunctionSymbol, Set<Rule>> ruleMap, final QTermSet Q, final boolean rNonOverlapping, final int maxSteps, final Set<TRSTerm> reachableTerms, final Set<TRSTerm> rFinalTerms) {
        if (!reachableTerms.add(t)) {
            return;
        }

        if (Globals.DEBUG_MPLUECKER && reachableTerms.size() % 500 == 0) {
            System.err.println("TERMS " + reachableTerms.size());
        }

        if (maxSteps == 0) {
            rFinalTerms.add(t);
        } else {
            final Set<TRSTerm> rewritten = this.rewrite(t, ruleMap, Q);
            if (rewritten.isEmpty()) {
                rFinalTerms.add(t);
            } else if (!rNonOverlapping) {
                for (final TRSTerm rt : rewritten) {
                    this.rewriteAsOftenAsPossible(rt, ruleMap, Q, rNonOverlapping, maxSteps - 1, reachableTerms, rFinalTerms);
                }
            } else {
                this.rewriteAsOftenAsPossible(rewritten.iterator().next(), ruleMap, Q, rNonOverlapping, maxSteps - 1, reachableTerms, rFinalTerms);
            }
        }
    }

    /**
     * returns all terms which result out of all possible rewritings in R.
     * The returned set may safely be modified.
     */
    public Set<TRSTerm> rewrite(final TRSTerm t, final Map<FunctionSymbol, ? extends Set<Rule>> R, final QTermSet Q) {
        final Set<TRSTerm> rewritings = new LinkedHashSet<TRSTerm>();
        Set<? extends Rule> usefulRules;
        for(final Pair<Position,TRSTerm> actPair : t.getPositionsWithSubTerms()) {
            final TRSTerm subterm = actPair.y;
            if(subterm.isVariable()) {
                continue;
            }
            final TRSFunctionApplication fSubterm = (TRSFunctionApplication) subterm;
            if((usefulRules = R.get(fSubterm.getRootSymbol())) == null) {
                continue;
            }
            for(final Rule actRule : usefulRules) {
                final TRSFunctionApplication lhs = actRule.getLeft();
                final TRSSubstitution matcher = lhs.getMatcher(subterm);
                if(matcher != null) {
                    final TRSTerm redex = actPair.y.applySubstitution(matcher);
                    if (!Q.canBeRewrittenBelowRoot(redex)) {
                        rewritings.add(t.replaceAt(actPair.x, actRule.getRight().applySubstitution(matcher)));
                    }
                }
            }
        }
        return rewritings;
    }


    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        return true;
    }




}
