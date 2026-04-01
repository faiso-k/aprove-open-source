package aprove.verification.oldframework.IntTRS.Compression;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Update the rule maps <code>rightRulesMap</code> and <code>leftRulesMap
 * </code> to entries for the rules from <code>rules</code>.
 */
public class RuleMaps {

    /*
     * rightRules maps each function symbol to the set of rules
     * which have that symbol as root symbol on the left hand side, i.e.,
     * which may rewrite terms with that symbol and thus can be used
     * as right side for our combination.
     *
     * leftRules maps each function symbol to the set of rules
     * which have that symbol _somewhere_ on the right hand side, so
     * that this symbol may be rewritten and the rule can be used on
     * the left hand side.
     */
    private CollectionMap<FunctionSymbol, IGeneralizedRule> rightRulesMap = new CollectionMap<>();
    private CollectionMap<FunctionSymbol, IGeneralizedRule> leftRulesMap = new CollectionMap<>();

    public RuleMaps(Collection<IGeneralizedRule> rules) {
        update(rules);
    }

    public void update(Collection<IGeneralizedRule> rules) {

        //Get all defined symbols:
        for (final IGeneralizedRule rule : rules) {
            final TRSFunctionApplication lhs = rule.getLeft();
            rightRulesMap.add(lhs.getRootSymbol(), rule);
        }

        //For all rhs, search for subterms:
        for (final IGeneralizedRule rule : rules) {
            final TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
            leftRulesMap.add(rhs.getRootSymbol(), rule);

            for (final TRSTerm t : rule.getRight().getSubTerms()) {
                if (t instanceof TRSFunctionApplication) {
                    final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                    //If this is a defined symbol, add it to our map:
                    if (rightRulesMap.containsKey(fa.getRootSymbol())) {
                        leftRulesMap.add(fa.getRootSymbol(), rule);
                    }
                }
            }
        }
    }

    public Collection<IGeneralizedRule> left(FunctionSymbol fs) {
        return leftRulesMap.getNotNull(fs);
    }

    public Collection<IGeneralizedRule> right(FunctionSymbol fs) {
        return rightRulesMap.getNotNull(fs);
    }

    public void unregisterFromRight(FunctionSymbol rootSymbol, IGeneralizedRule rule) {
        rightRulesMap.removeFromCollection(rootSymbol, rule);
    }

    public void unregisterFromLeft(FunctionSymbol rootSymbol, IGeneralizedRule rule) {
        leftRulesMap.removeFromCollection(rootSymbol, rule);
    }

    public void remove(FunctionSymbol fs) {
        leftRulesMap.remove(fs);
        rightRulesMap.remove(fs);
    }

    public void checkValidity(Set<IGeneralizedRule> rules) {
      //Check if the map only contain existing rules:
        for (final FunctionSymbol sym : leftRulesMap.keySet()) {
            for (final IGeneralizedRule rule : leftRulesMap.get(sym)) {
                assert (rules.contains(rule)) : "Have rule in left rule cache which was removed";
            }
        }

        for (final FunctionSymbol sym : rightRulesMap.keySet()) {
            for (final IGeneralizedRule rule : rightRulesMap.get(sym)) {
                assert (rules.contains(rule)) : "Have rule in right rule cache which was removed";
            }
        }
    }

}
