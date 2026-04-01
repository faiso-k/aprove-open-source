package aprove.verification.dpframework.CSDPProblem;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/* FIXME move to appropriate package */
/**
 * A generalized TRS is a set TermPairs, which have no restrictions on
 * variables.
 *
 * @author fab
 * @version $Id$
 */
public class GeneralizedTRS implements Iterable<TermPair> {

    /**
     * Contains all rules, used to iterate.
     */
    private final ImmutableSet<TermPair> rules;

    /**
     * Mapping from symbols to rules with the symbols as root symbol of their
     * lhs. For performance, no need to search linearly through rules.
     */
    private final ImmutableMap<FunctionSymbol, ImmutableSet<TermPair>> symbolToRule;

    /**
     * Stores all rules which have a variable as their lhs.
     */
    private final ImmutableSet<TermPair> varRules;

    private GeneralizedTRS(ImmutableSet<TermPair> rules) {
        this.rules = rules;

        Set<TermPair> mutableVarRules = new LinkedHashSet<TermPair>();
        Map<FunctionSymbol, Set<TermPair>> mutableSymbolToRule = new LinkedHashMap<FunctionSymbol, Set<TermPair>>();
        for (TermPair rule : rules) {
            TRSTerm lhs = rule.getLeft();
            if (lhs.isVariable()) {
                mutableVarRules.add(rule);
            } else {
                FunctionSymbol f = ((TRSFunctionApplication) lhs).getRootSymbol();
                Set<TermPair> fRules = mutableSymbolToRule.get(f);
                if (fRules == null) {
                    fRules = new LinkedHashSet<TermPair>();
                    mutableSymbolToRule.put(f, fRules);
                }
                fRules.add(rule);
            }
        }

        this.varRules = ImmutableCreator.create(mutableVarRules);

        Map<FunctionSymbol, ImmutableSet<TermPair>> mutableSymbolToRule2 = new LinkedHashMap<FunctionSymbol, ImmutableSet<TermPair>>();
        for (Map.Entry<FunctionSymbol, Set<TermPair>> e : mutableSymbolToRule
                .entrySet()) {
            mutableSymbolToRule2.put(e.getKey(), ImmutableCreator.create(e
                    .getValue()));
        }
        this.symbolToRule = ImmutableCreator.create(mutableSymbolToRule2);
    }

    /**
     * Creates a new GeneralizedTRS from a Set of TermPairs.
     *
     * @param rules
     * @return
     */
    public static GeneralizedTRS create(ImmutableSet<TermPair> rules) {
        return new GeneralizedTRS(rules);
    }

    /**
     * Creates a new GeneralizedTRS from a Set of Rules.
     *
     * @param rules
     * @return
     */
    public static GeneralizedTRS create(Set<Rule> rules) {
        Set<TermPair> newRules = new LinkedHashSet<TermPair>();
        for (Rule r : rules) {
            TermPair p = TermPair.create(r.getLeft(), r.getRight());
            newRules.add(p);
        }
        return new GeneralizedTRS(ImmutableCreator.create(newRules));
    }

    /**
     * Iterator over all rules in this GeneralizedTRS.
     */
    @Override
    public Iterator<TermPair> iterator() {
        return this.rules.iterator();
    }

    public final ImmutableSet<TermPair> getRules() {
        return this.rules;
    }

    /**
     * Returns a mapping from function symbol to TermPairs with this function
     * symbol as root symbol of their lhs. Can be used for fast lookups.
     *
     * @return
     */
    public final ImmutableMap<FunctionSymbol, ImmutableSet<TermPair>> getSymbolToRule() {
        return this.symbolToRule;
    }

    /**
     * Returns rules whose lhs are variables.
     *
     * @return
     */
    public final ImmutableSet<TermPair> getVarRules() {
        return this.varRules;
    }
}
