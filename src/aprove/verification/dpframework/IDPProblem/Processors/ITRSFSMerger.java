package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public abstract class ITRSFSMerger extends ITRSProcessor {

    @Override
    public boolean isITRSApplicable(final ITRSProblem itrs) {
        return true;
    }

    @Override
    protected Result processITRSProblem(final ITRSProblem itrs, final Abortion aborter)
            throws AbortionException {

        final Pair<Map<Set<FunctionSymbol>, FunctionSymbol>, YNMImplication> mergeClasses = this.getMergeClasses(itrs, aborter);
        aborter.checkAbortion();


        final Map<Set<FunctionSymbol>, FunctionSymbol> merges = mergeClasses.x;

        if (merges.isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        final Set<GeneralizedRule> newRules = ITRSFSMerger.mergeRules(itrs.getPredefinedMap(), itrs.getR(), merges, aborter);

        aborter.checkAbortion();
        final Set<TRSFunctionApplication> newQTerms = ITRSFSMerger.mergeTerms(itrs.getPredefinedMap(), itrs.getQ().getWrappedQ().getTerms(), merges, aborter);

        final RuleAnalysis<GeneralizedRule> newRuleAna = new RuleAnalysis<GeneralizedRule>(
                ImmutableCreator.create(newRules), itrs.getPredefinedMap());

        final IQTermSet newQ = new IQTermSet(new QTermSet(newQTerms), itrs.getPredefinedMap());
        final ITRSProblem newItrs = ITRSProblem.create(newRuleAna, newQ);

        final ITRSFSMergerProof proof =
            new ITRSFSMergerProof(merges);

        return ResultFactory.proved(newItrs, YNMImplication.SOUND, proof);
    }

    public static Set<GeneralizedRule> mergeRules(final IDPPredefinedMap predefinedMap,
        final Set<GeneralizedRule> rules,
        final Map<Set<FunctionSymbol>, FunctionSymbol> merges,
        final Abortion aborter)
            throws AbortionException {
        final boolean hasMerges = ITRSFSMerger.checkMerges(predefinedMap, merges);

        if (!hasMerges) {
            return rules;
        }

        aborter.checkAbortion();
        final Set<GeneralizedRule> newRules = new LinkedHashSet<GeneralizedRule>();
        for (final GeneralizedRule rule : rules) {
            newRules.add(ITRSFSMerger.mergeFs(rule, merges));
        }
        return newRules;
    }

    public static <T extends TRSTerm> Set<T> mergeTerms(final IDPPredefinedMap predefinedMap,
        final Set<T> terms,
        final Map<Set<FunctionSymbol>, FunctionSymbol> merges,
        final Abortion aborter)
            throws AbortionException {
        final boolean hasMerges = ITRSFSMerger.checkMerges(predefinedMap, merges);

        if (!hasMerges) {
            return terms;
        }

        aborter.checkAbortion();
        final Set<T> newTerms = new LinkedHashSet<T>();
        for (final T term : terms) {
            newTerms.add(ITRSFSMerger.mergeFs(term, merges));
        }
        return newTerms;
    }

    private static boolean checkMerges(final IDPPredefinedMap predefinedMap,
        final Map<Set<FunctionSymbol>, FunctionSymbol> merges) {
        boolean hasMerges = false;
        if (Globals.useAssertions) {
            for (final Collection<FunctionSymbol> merge : merges.keySet()) {
                if (merge.size() > 1) {
                    hasMerges = true;
                }
                for (final FunctionSymbol fs : merge) {
                    assert !predefinedMap.isPredefined(fs) : "can not merge pre-defined function symbols";
                }
            }
        }
        return hasMerges;
    }


    protected abstract Pair<Map<Set<FunctionSymbol>, FunctionSymbol>, YNMImplication> getMergeClasses(
            ITRSProblem itrs, Abortion aborter) throws AbortionException;

    private static GeneralizedRule mergeFs(final GeneralizedRule rule,
            final Map<Set<FunctionSymbol>, FunctionSymbol> merges) {
        return GeneralizedRule.create(ITRSFSMerger.mergeFs(rule.getLeft(), merges), ITRSFSMerger.mergeFs(rule.getRight(), merges));
    }

    @SuppressWarnings(value = { "unchecked" })
    private static <T extends TRSTerm> T mergeFs(final T term,
            final Map<Set<FunctionSymbol>, FunctionSymbol> merges) {
        if (term.isVariable()) {
            return term;
        } else {
            final TRSFunctionApplication fa = (TRSFunctionApplication) term;
            final FunctionSymbol root = fa.getRootSymbol();
            FunctionSymbol newRoot = root;
            for (final Map.Entry<Set<FunctionSymbol>, FunctionSymbol> merge : merges.entrySet()) {
                if (merge.getKey().contains(root)) {
                    newRoot = merge.getValue();
                    break;
                }
            }
            boolean changedArgs = false;
            final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
            for (final TRSTerm arg : fa.getArguments()) {
                final TRSTerm newArg = ITRSFSMerger.mergeFs(arg, merges);
                if (newArg != arg) {
                    changedArgs = true;
                }
                newArgs.add(newArg);
            }
            if (root != newRoot || changedArgs) {
                return (T) TRSTerm.createFunctionApplication(newRoot, newArgs);
            } else {
                return term;
            }
        }
    }



    public static class ITRSFSMergerProof extends DefaultProof {

        private final Map<Set<FunctionSymbol>, FunctionSymbol> merges;

        public ITRSFSMergerProof(final Map<Set<FunctionSymbol>, FunctionSymbol> merges) {
            this.merges = merges;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder("The following function symbols have been merged:");
            sb.append(o.linebreak());
            sb.append(o.tableStart(3));
            for (final Map.Entry<Set<FunctionSymbol>, FunctionSymbol> merge : this.merges.entrySet()) {
                final ArrayList<String> row = new ArrayList<String>(4);
                row.add(o.set(merge.getKey(), Export_Util.NICE_SET));
                row.add(" > ");
                row.add(merge.getValue().toString());
                sb.append(o.tableRow(row));
            }
            sb.append(o.tableEnd());
            return sb.toString();
        }
    }
}