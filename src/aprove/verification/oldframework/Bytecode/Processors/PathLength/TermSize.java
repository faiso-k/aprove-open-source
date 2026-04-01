package aprove.verification.oldframework.Bytecode.Processors.PathLength;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * This can be used to replace terms encoding objects by integers which only
 * represent the "term size" of the corresponding object.
 *
 * @author Felix Bier
 */
public final class TermSize {

    /** Utility functions. */
    private final PathLengthUtil util;

    /** Set of rules to be transformed. */
    private Set<IGeneralizedRule> rules;

    /** Set of defined symbols. */
    private Set<FunctionSymbol> definedSymbols;

    private LinkedHashSet<IGeneralizedRule> resultRules;

    /**
     * Constructor.
     * @param predefMap some predefined map
     */
    private TermSize(final IDPPredefinedMap predefMap) {
       this.util = new PathLengthUtil(predefMap);
    }

    /**
     * Translates a set of IGeneralizedRule.
     * @param igRules a set of some IGeneralizedRule
     * @param predefMap some IDPPredefinedMap or null [then we use the default map]
     * @return a set of IGeneralizedRule
     */
    public static Set<IGeneralizedRule> translateIGRuleSet(
        final Set<IGeneralizedRule> igRules,
        final IDPPredefinedMap predefMap)
    {
        if (igRules == null) {
            return null;
        }

        final IDPPredefinedMap predefinedMap = (predefMap == null) ? IDPPredefinedMap.DEFAULT_MAP : predefMap;
        final TermSize converter = new TermSize(predefinedMap);

        final Set<IGeneralizedRule> outputRules = converter.convertIGRules(igRules);
        return outputRules;
    }

    /**
     * Converts a set of IGeneralizedRules.
     * @param igRules set of rules
     * @return set of converted rules
     */
    private Set<IGeneralizedRule> convertIGRules(final Set<IGeneralizedRule> igRules) {

        if (Globals.DEBUG_FBIER) {
            System.err.println();
            System.err.println("Pre:");
            for (final IGeneralizedRule igRule : igRules) {
                System.err.println(igRule);
            }
            System.err.println();
        }

        this.rules = igRules;
        this.findDefinedSymbols();
        this.translateRules();

        if (Globals.DEBUG_FBIER) {
            System.err.println();
            System.err.println("Post:");
            for (final IGeneralizedRule igRule : this.resultRules) {
                System.err.println(igRule);
            }
            System.err.println();
        }

        return this.resultRules;
    }

    /**
     * Finds the defined symbols.
     */
    private void findDefinedSymbols() {
        this.definedSymbols = new LinkedHashSet<FunctionSymbol>(this.rules.size());
        for (final IGeneralizedRule rule : this.rules) {
            this.definedSymbols.add(rule.getLeft().getRootSymbol());
        }

        // TODO END_OF_CLASS, CYCLIC_INSTANCE_TERM ?
        assert !this.definedSymbols.contains(this.util.JAVA_LANG_OBJECT_SYMBOL)
            && !this.definedSymbols.contains(this.util.ARRAY_CONSTR)
            && !this.definedSymbols.contains(this.util.NULL) : "Strange rules!!";
    }

    /**
     * Translates the rules. For each rule a instance of RuleTransformation
     * is created, which will do the work.
     */
    private void translateRules() {
        this.resultRules = new LinkedHashSet<IGeneralizedRule>(this.rules.size());
        for (final IGeneralizedRule iRule : this.rules) {
            final TermSizeTransformation transformer = new TermSizeTransformation(iRule, this.util, this.definedSymbols);
            final IGeneralizedRule newRule = transformer.transform();
            this.resultRules.add(newRule);
        }
    }
}
