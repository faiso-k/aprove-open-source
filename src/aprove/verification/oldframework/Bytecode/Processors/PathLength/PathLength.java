package aprove.verification.oldframework.Bytecode.Processors.PathLength;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This can be used to replace terms encoding objects by integer(s) which only represent
 * the "path length" of the corresponding object.
 *
 * @author Matthias Hoelzel
 */

public final class PathLength {
    /** Name generator */
    private final FreshNameGenerator ng;

    /** Utility functions. */
    private final PathLengthUtil util;

    /** Set of rules to be transformed. */
    private Set<IGeneralizedRule> rules;

    /** Resulting rules. */
    private Set<IGeneralizedRule> resultRules;

    /** Set of defined symbols. */
    private Set<FunctionSymbol> definedSymbols;

    /** The typing we inferred. */
    private LinkedHashMap<FunctionSymbol, ArrayList<TRSTerm>> typing;

    /**
     * YAY! It is a constructor!
     * @param predefMap some predefined map
     */
    private PathLength(final IDPPredefinedMap predefMap) {
        this.ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
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
        final PathLength converter = new PathLength(predefinedMap);

        final Set<IGeneralizedRule> outputRules = converter.convertIGRules(igRules);
        return outputRules;
    }

    /**
     * Translates a set of some GeneralizedRule
     * @param gRules a set of generalized rules
     * @param predefMap some IDPPredefinedMap or null [then we use the default map]
     * @return a set of translated generalized rules
     */
    public static Set<GeneralizedRule> translateRuleSet(
        final Set<GeneralizedRule> gRules,
        final IDPPredefinedMap predefMap)
    {
        if (gRules == null) {
            return null;
        }

        final IDPPredefinedMap predefinedMap = (predefMap == null) ? IDPPredefinedMap.DEFAULT_MAP : predefMap;
        final PathLength converter = new PathLength(predefinedMap);
        return converter.convertGRules(gRules);
    }

    /**
     * Converts a set of generalized rules.
     * @param gRules set of rules
     * @return set of converted rules
     */
    private Set<GeneralizedRule> convertGRules(final Set<GeneralizedRule> gRules) {
        // 1. Convert the rules into IGeneralizedRules
        final Set<IGeneralizedRule> igRules = new LinkedHashSet<IGeneralizedRule>(gRules.size());
        for (final GeneralizedRule gRule : gRules) {
            final IGeneralizedRule igRule = IGeneralizedRule.create(gRule.getLeft(), gRule.getRight(), null);
            igRules.add(igRule);
        }

        // 2. Apply transformation at these rules
        final Set<IGeneralizedRule> convertedRules = this.convertIGRules(igRules);

        // 3. Remove conditions and return:
        return IGeneralizedRule.removeConditions(convertedRules, true);
    }

    /**
     * Converts a set of IGeneralizedRules.
     * @param igRules set of rules
     * @return set of converted rules
     */
    private Set<IGeneralizedRule> convertIGRules(final Set<IGeneralizedRule> igRules) {
        // 0. Debug dump:
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("pathlength");
            l.logln("Here are the rules:");
            for (final IGeneralizedRule igRule : igRules) {
                l.logln(igRule);
            }
            l.logln();
        }

        this.rules = igRules;

        // 1. Prepare the rules:
        this.renameVariables();
        this.findDefinedSymbols();
        this.symbolTransformation();

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("pathlength");
            l.logln("Here are the prepared rules");
            for (final IGeneralizedRule igRule : this.rules) {
                l.logln(igRule);
            }
        }

        // 2. Try to deduce as much type information as possible
        this.typeCheck();

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("pathlength");
            l.logln("\nHere is the typing:");
            for (final FunctionSymbol sym : this.definedSymbols) {
                l.logln("" + sym + " -> " + this.typing.get(sym));
            }
        }

        // 3. Translate rules:
        this.translateRules();

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("pathlength");
            l.logln("\nAnd here is the result:");
            for (final IGeneralizedRule igRule : this.resultRules) {
                l.logln(igRule);
            }
            DebugLogger.finishLog("pathlength");
        }

        return this.resultRules;
    }

    /**
     * Renames the variable to ensure, that two different rules use different variables.
     * Will also replace null condition terms by TRUE.
     */
    private void renameVariables() {
        final LinkedHashSet<IGeneralizedRule> renamedRules = new LinkedHashSet<IGeneralizedRule>(this.rules.size());
        for (final IGeneralizedRule iRule : this.rules) {
            renamedRules.add(ToolBox.renameVariablesInRule(iRule, this.ng));
        }
        this.rules = renamedRules;
    }

    /**
     * Finds the defined symbols.
     */
    private void findDefinedSymbols() {
        this.definedSymbols = new LinkedHashSet<FunctionSymbol>(this.rules.size());
        for (final IGeneralizedRule rule : this.rules) {
            this.definedSymbols.add(rule.getLeft().getRootSymbol());
        }

        assert !this.definedSymbols.contains(this.util.JAVA_LANG_OBJECT_SYMBOL)
            && !this.definedSymbols.contains(this.util.END_OF_CLASS)
            && !this.definedSymbols.contains(this.util.ARRAY_CONSTR)
            && !this.definedSymbols.contains(this.util.NULL) : "Strange rules!!";
    }

    /**
     * Replaces nested defined symbols by fresh variables.
     * Furthermore it checks whether or not exactly one function symbol occurs
     * at the left or right side.
     */
    private void symbolTransformation() {
        final LinkedHashSet<IGeneralizedRule> transformedRules = new LinkedHashSet<IGeneralizedRule>(this.rules.size());
        for (final IGeneralizedRule iRule : this.rules) {
            final TRSTerm newRight = this.removeNestedDefinedSymbols(iRule.getRight(), true);
            if (newRight instanceof TRSFunctionApplication) {
                final TRSFunctionApplication newLeft =
                    (TRSFunctionApplication) this.removeNestedDefinedSymbols(iRule.getLeft(), true);
                final TRSTerm condition = iRule.getCondTerm();
                transformedRules.add(IGeneralizedRule.create(newLeft, newRight, condition));
            }
        }
        this.rules = transformedRules;
    }

    /**
     * Replaces nested defined symbols by fresh variables.
     * @param t current term to be transformed
     * @return another term
     */
    private TRSTerm removeNestedDefinedSymbols(final TRSTerm t, final boolean firstLayer) {
        if (t.isVariable()) {
            return t;
        } else {
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol sym = func.getRootSymbol();
            if (!firstLayer && this.definedSymbols.contains(sym)) {
                return TRSTerm.createVariable(this.ng.getFreshName("n", false));
            } else {
                final ImmutableList<TRSTerm> args = func.getArguments();
                final ArrayList<TRSTerm> newArguments = new ArrayList<TRSTerm>(args.size());
                for (int i = 0; i < args.size(); i++) {
                    newArguments.add(this.removeNestedDefinedSymbols(
                        args.get(i),
                        firstLayer && !this.definedSymbols.contains(func.getRootSymbol())));
                }
                return TRSTerm.createFunctionApplication(sym, newArguments);
            }
        }
    }

    /**
     * Performs a dedicated type check to determine the type of the function symbols.
     */
    private void typeCheck() {
        // 0. Initialize:
        this.typing = new LinkedHashMap<FunctionSymbol, ArrayList<TRSTerm>>(this.definedSymbols.size());
        for (final FunctionSymbol defSym : this.definedSymbols) {
            final ArrayList<TRSTerm> types = new ArrayList<TRSTerm>(defSym.getArity());
            for (int i = 0; i < defSym.getArity(); i++) {
                types.add(TRSTerm.createVariable(this.ng.getFreshName("t", false)));
            }
            this.typing.put(defSym, types);
        }

        // 1. Build the unification system to be solved:
        final LinkedList<Pair<TRSTerm, TRSTerm>> uniSystem = new LinkedList<Pair<TRSTerm, TRSTerm>>();
        for (final IGeneralizedRule iRule : this.rules) {
            final TRSFunctionApplication left = iRule.getLeft();
            final TRSFunctionApplication right = (TRSFunctionApplication) iRule.getRight();

            this.getTypeRequirements(left, uniSystem);
            this.getTypeRequirements(right, uniSystem);

            for (final TRSVariable v : iRule.getCondTerm().getVariables()) {
                uniSystem.add(new Pair<TRSTerm, TRSTerm>(v, this.util.PREDEFINED_TYPE));
            }
        }

        // 2. Get solution:
        TRSSubstitution mgu = TRSSubstitution.create();
        for (final Pair<TRSTerm, TRSTerm> u : uniSystem) {
            final TRSTerm x = u.x.applySubstitution(mgu);
            final TRSTerm y = u.y.applySubstitution(mgu);

            final TRSSubstitution next = x.getMGU(y);

            if (next == null) {
                mgu = null;
                break;
            }

            mgu = mgu.compose(next);
        }
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("pathlength");
            l.logln(mgu);
        }

        // 3. Interpret result
        if (mgu != null) {
            for (final ArrayList<TRSTerm> arr : this.typing.values()) {
                for (int i = 0; i < arr.size(); i++) {
                    arr.set(i, arr.get(i).applySubstitution(mgu));
                }
            }
        }
    }

    /**
     * Builds the unification system, from that we can derive the types.
     * @param func current function application
     * @param uniSystem system to be built
     */
    private void getTypeRequirements(final TRSFunctionApplication func, final LinkedList<Pair<TRSTerm, TRSTerm>> uniSystem) {
        final FunctionSymbol sym = func.getRootSymbol();
        if (!this.definedSymbols.contains(sym)) {
            for (final TRSTerm t : func.getArguments()) {
                if (t instanceof TRSFunctionApplication) {
                    this.getTypeRequirements((TRSFunctionApplication) t, uniSystem);
                }
            }
        } else {
            final ArrayList<TRSTerm> types = this.typing.get(sym);

            for (int i = 0; i < types.size(); i++) {
                uniSystem.add(new Pair<TRSTerm, TRSTerm>(types.get(i), this.util.getType(func.getArgument(i))));
            }
        }
    }

    /**
     * Translates the rules. For each rule a instance of RuleTransformation
     * is created, which will do the work.
     */
    private void translateRules() {
        this.resultRules = new LinkedHashSet<IGeneralizedRule>(this.rules.size());
        for (final IGeneralizedRule iRule : this.rules) {
            final RuleTransformation transformer = new RuleTransformation(iRule, this.ng, this.typing, this.util);
            final IGeneralizedRule newRule = transformer.transform();
            this.resultRules.add(newRule);
        }
    }
}
