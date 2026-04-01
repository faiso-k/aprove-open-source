package aprove.verification.oldframework.IntTRS.BoundedInts;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import immutables.*;

/**
 * Maps for every rule variables to some BoundedDomain. This should represent,
 * that the given variable is interpreted by some value from the corresponding
 * domain. Variables, not mentioned are assumed to be unbounded.
 * @author Matthias Hoelzel
 */
public class BoundInformation {
    /** Awesome bound information! */
    private final ImmutableLinkedHashMap<IGeneralizedRule, ImmutableLinkedHashMap<TRSVariable, IntegerType>> boundInformationMap;

    /** What are the domains of the arguments. */
    private final ImmutableLinkedHashMap<FunctionSymbol, ArrayList<IntegerType>> argumentDomains;

    /**
     * Constructor!
     * @param boundInfoMap maps rules to maps, mapping variables to bounded
     * domains
     */
    public BoundInformation(
            final ImmutableLinkedHashMap<IGeneralizedRule, ImmutableLinkedHashMap<TRSVariable, IntegerType>> boundInfoMap) {
        this.boundInformationMap = boundInfoMap;

        this.argumentDomains = ImmutableCreator.create(this.inferArgumentDomains());
    }

    /**
     * Infers the domains of the arguments.
     * @return map
     */
    private LinkedHashMap<FunctionSymbol, ArrayList<IntegerType>> inferArgumentDomains() {
        final LinkedHashMap<FunctionSymbol, ArrayList<IntegerType>> argDomains = new LinkedHashMap<>();
        for (final Entry<IGeneralizedRule, ImmutableLinkedHashMap<TRSVariable, IntegerType>> e : this.boundInformationMap.entrySet()) {
            final IGeneralizedRule rule = e.getKey();
            final TRSFunctionApplication left = rule.getLeft();
            final FunctionSymbol sym = left.getRootSymbol();
            final ImmutableList<TRSTerm> args = left.getArguments();
            final ArrayList<IntegerType> domains = new ArrayList<>(args.size());
            for (final TRSTerm arg : args) {
                assert arg instanceof TRSVariable : "Term on the left side!";
                final TRSVariable v = (TRSVariable) arg;
                if (this.boundInformationMap.containsKey(rule) && this.boundInformationMap.get(rule).containsKey(v)) {
                    domains.add(this.boundInformationMap.get(rule).get(v));
                } else {
                    domains.add(null);
                }
            }
            if (argDomains.containsKey(sym)) {
                assert argDomains.get(sym).equals(domains) : "Inconsistent bounds: " + argDomains.get(sym) + " vs. "
                    + domains;
            } else {
                argDomains.put(sym, domains);
            }
        }
        return argDomains;
    }

    /**
     * Getter for boundInformationMap.
     * @return some strange map
     */
    public ImmutableLinkedHashMap<IGeneralizedRule, ImmutableLinkedHashMap<TRSVariable, IntegerType>> getBoundInformationMap() {
        return this.boundInformationMap;
    }

    /**
     * Useful for renaming the variables. This method will return a renamed
     * version of this.
     * @param substitution maps Variable to Variables
     * @param ruleReplacement replacement of the rules
     * @return BoundInformation
     */
    public BoundInformation renameVariables(final Map<TRSVariable, TRSVariable> substitution,
        final Map<IGeneralizedRule, IGeneralizedRule> ruleReplacement) {
        final LinkedHashMap<IGeneralizedRule, ImmutableLinkedHashMap<TRSVariable, IntegerType>> newBoundMap =
            new LinkedHashMap<>(this.boundInformationMap.size());

        for (final Entry<IGeneralizedRule, ImmutableLinkedHashMap<TRSVariable, IntegerType>> e : this.boundInformationMap.entrySet()) {
            final IGeneralizedRule rule = e.getKey();
            final ImmutableLinkedHashMap<TRSVariable, IntegerType> currentMap = e.getValue();
            final LinkedHashMap<TRSVariable, IntegerType> newMap = new LinkedHashMap<>(currentMap.size());
            for (final Entry<TRSVariable, IntegerType> vb : currentMap.entrySet()) {
                newMap.put(substitution.get(vb.getKey()), vb.getValue());
            }
            assert newMap.size() == currentMap.size() : "Non-injective substitution!";
            assert ruleReplacement.containsKey(rule) : "Invalid rule replacement! " + rule;
            newBoundMap.put(ruleReplacement.get(rule), ImmutableCreator.create(newMap));
        }
        return new BoundInformation(ImmutableCreator.create(newBoundMap));
    }
}
