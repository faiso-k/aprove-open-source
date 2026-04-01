package aprove.verification.oldframework.IntTRS.Compression;

import static java.util.stream.Collectors.*;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IRSwT.*;
import aprove.verification.oldframework.IRSwT.IRSwTFormatTransformer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Use rule combination to reduce the number of rules.
 */
public class RuleCombiner {

    // rules set to combine
    private Set<IGeneralizedRule> rules;
    //set of function symbols that shouldn't be removed in the combination (typically, start points
    // of methods that are called from a different rule set)
    private Set<FunctionSymbol> dontRemove;
    private IDPPredefinedMap predefinedMap;
    private RoundingBehaviour roundingBehaviour;
    private Abortion aborter;
    protected final SymbolRemover symbolRemover;

    public RuleCombiner(Set<IGeneralizedRule> rules,
            Set<FunctionSymbol> dontRemove,
            IDPPredefinedMap predefinedMap,
            RoundingBehaviour roundingBehaviour,
            Abortion aborter,
            Map<IGeneralizedRule, Pair<IGeneralizedRule,IGeneralizedRule>> combinedRulesMap) {
        this.rules = rules;
        this.dontRemove = dontRemove;
        this.predefinedMap = predefinedMap;
        this.roundingBehaviour = roundingBehaviour;
        this.aborter = aborter;
        this.symbolRemover = new SymbolRemover(rules, predefinedMap, aborter, combinedRulesMap);
    }

    public RuleCombiner(Set<IGeneralizedRule> rules,
            Set<FunctionSymbol> dontRemove,
            Abortion aborter, Map<IGeneralizedRule, Pair<IGeneralizedRule,IGeneralizedRule>> combinedRulesMap) {
        this(rules, dontRemove, IDPPredefinedMap.DEFAULT_MAP, RoundingBehaviour.UNKNOWN, aborter, combinedRulesMap);
    }
    
    public RuleCombiner(Set<IGeneralizedRule> rules,
            Set<FunctionSymbol> dontRemove,
            IDPPredefinedMap predefinedMap,
            RoundingBehaviour roundingBehaviour,
            Abortion aborter) {
        this.rules = rules;
        this.dontRemove = dontRemove;
        this.predefinedMap = predefinedMap;
        this.roundingBehaviour = roundingBehaviour;
        this.aborter = aborter;
        this.symbolRemover = new SymbolRemover(rules, predefinedMap, aborter);
    }

    public RuleCombiner(Set<IGeneralizedRule> rules,
            Set<FunctionSymbol> dontRemove,
            Abortion aborter) {
        this(rules, dontRemove, IDPPredefinedMap.DEFAULT_MAP, RoundingBehaviour.UNKNOWN, aborter);
    }

    public Pair<Boolean, Set<IGeneralizedRule>> combineRules(boolean filterFreeVarsFromCond, boolean cleanConstraints) {
    	return combineRules(filterFreeVarsFromCond, cleanConstraints, cleanConstraints);
    }
    
    /**@param removeDivMod if cleanConstraints is set, should we remove DIV and MOD from rules?
     * @param filterFreeVarsFromCond if true, free variables in the conditions are removed
     */
    public Pair<Boolean, Set<IGeneralizedRule>> combineRules(
    		boolean filterFreeVarsFromCond,
    		boolean cleanConstraints,
    		boolean removeDivMod) {
        boolean changedAtAll = false;
        boolean changed = false;
        do {
            aborter.checkAbortion();
            changed = false;
            final Collection<FunctionSymbol> definedSymbols = getSymbolsToRemove();
            for (final FunctionSymbol fs : definedSymbols) {
                if (dontRemove.contains(fs)) {
                    continue;
                }
                changed |= symbolRemover.tryToRemoveSymbol(fs, filterFreeVarsFromCond);
            }
            changedAtAll |= changed;
        } while (changed);

        Set<IGeneralizedRule> resultingRules = symbolRemover.getResult();
        Set<IGeneralizedRule> cleanedRules = new LinkedHashSet<>();

        if (cleanConstraints) {
            for (IGeneralizedRule r: resultingRules) {
                cleanedRules.addAll(IRSwTFormatTransformer.removeDivModAndNotAndNotEqualAndOrAndFalse(r, roundingBehaviour, predefinedMap, false, removeDivMod));
            }
            cleanedRules = TerminationSCCToIDPv1Processor.cleanConstraints(cleanedRules, dontRemove, false, false, predefinedMap, aborter);
        } else {
            cleanedRules = resultingRules;
        }
        cleanedRules =TerminationSCCToIDPv1Processor.removeTrivialConstraints(cleanedRules, predefinedMap);
        return new Pair<>(changedAtAll || !resultingRules.equals(cleanedRules), cleanedRules);
    }

    // For some reason, this seems to implement a good heuristic to determine
    // the order in which we try to remove defined symbols...
    private Collection<FunctionSymbol> getSymbolsToRemove() {
        Set<FunctionSymbol> defined = rules.stream().map(x -> x.getRootSymbol()).collect(toSet());
        Set<FunctionSymbol> res = new LinkedHashSet<>();
        for (IGeneralizedRule rule : rules) {
            for (TRSTerm t : rule.getRight().getSubTerms()) {
                if (t instanceof TRSFunctionApplication) {
                    TRSFunctionApplication fa = (TRSFunctionApplication) t;
                    if (defined.contains(fa.getRootSymbol())) {
                        res.add(fa.getRootSymbol());
                    }
                }
            }
        }
        return res;
    }

}
