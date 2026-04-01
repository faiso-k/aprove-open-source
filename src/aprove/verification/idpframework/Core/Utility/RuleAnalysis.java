/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Core.Utility;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Algorithms.Confluence.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * This class provides methods to analyze sets of rules. Generated once all
 * values are cached.
 * @author mpluecke
 */
public class RuleAnalysis<R extends IRule> implements Immutable, Exportable,
        IDPExportable {

    public static <Q extends IRule> RuleAnalysis<Q> emptyAnalysis() {
        return new RuleAnalysis<Q>(
            ImmutableCreator.create(java.util.Collections.<Q> emptySet()),
            IDPPredefinedMap.EMPTY_MAP, new SharingPolyFactory());
    }

    protected static final ImmutableSet<IFunctionApplication<?>> EMPTY_FUNCTIONAPP_SET =
        ImmutableCreator.create(java.util.Collections.<IFunctionApplication<?>> emptySet());

    private final ImmutableSet<R> rules;
    private final PolyFactory polyFactory;
    private final IDPPredefinedMap predefinedMap;
    private volatile ImmutableSet<IFunctionSymbol<?>> rootSymbols;
    private volatile ImmutableSet<IFunctionSymbol<?>> functionSymbols;
    private volatile ImmutableSet<IVariable<?>> variables;
    private volatile ImmutableSet<PredefinedSemantics<?>> predefinedFunctions;
    private volatile ImmutableSet<IFunctionApplication<?>> leftHandSides;
    private volatile ImmutableMap<IFunctionSymbol<?>, ImmutableSet<IFunctionApplication<?>>> rootToLeftHandSides;
    private volatile ImmutableSet<ITerm<?>> terms;
    private volatile ImmutableSet<Domain> domains;
    // private volatile ImmutableSet<UnconditionalIRule> dependencyPairs;
    // private volatile FreshNameGenerator dpFreshNames;
    // private volatile Map<IFunctionSymbol<?>, IFunctionSymbol<?>> dpSymbolToFreshSymbol;
    private volatile ImmutableSet<IFunctionApplication<?>> standardLeftHandSides;
    private volatile ImmutableMap<IFunctionSymbol<?>, ImmutableSet<IFunctionApplication<?>>> rootToStandardLeftHandSides;
    private volatile ImmutableMap<IFunctionSymbol<?>, ImmutableSet<R>> ruleMap;
    private volatile ImmutableMap<IFunctionSymbol<?>, ImmutableSet<R>> reverseRuleMap;
    private volatile Map<ImmutableSet<R>, CriticalPairs> criticalPairs;
    private volatile Boolean satVarCondition;

    /**
     * R set contains restricted integers. (computed by getDomains)
     */
    private boolean restricted;

    /**
     * R set contains unrestricted integers. (computed by getDomains)
     */
    private boolean unrestricted;

    /**
     * R set contains bitwise predefined functions. (computed by
     * getPredefinedFunctions)
     */
    private boolean bitwise;

    /**
     * R set contains predefined defined functions (as opposed to integer or
     * boolean constants as predefined symbols only) (computed by
     * getPredefinedFunctions)
     */
    private boolean predefinedDefSymbols;

    public RuleAnalysis(final ImmutableSet<R> rules,
            final IDPPredefinedMap predefinedMap, final PolyFactory polyFactory) {
        this.rules = rules;
        this.polyFactory = polyFactory;
        this.predefinedMap = predefinedMap;
        this.criticalPairs = new HashMap<ImmutableSet<R>, CriticalPairs>();
    }

    /**
     * Returns the user-defined rules that are analyzed.
     */
    public ImmutableSet<R> getRules() {
        return this.rules;
    }

    /**
     * @return the map of pre-defined function symbols
     */
    public IDPPredefinedMap getPredefinedMap() {
        return this.predefinedMap;
    }

    /**
     * @return the map of pre-defined function symbols
     */
    public PolyFactory getPolyFactory() {
        return this.polyFactory;
    }

    /**
     * Extracts all function symbols that occur in the user-defined rules.
     * @return
     */
    public ImmutableSet<IFunctionSymbol<?>> getFunctionSymbols() {
        if (this.functionSymbols == null) {
            synchronized (this) {
                if (this.functionSymbols == null) {
                    final Set<IFunctionSymbol<?>> fs =
                        new LinkedHashSet<IFunctionSymbol<?>>();
                    for (final IRule rule : this.rules) {
                        fs.addAll(rule.getFunctionSymbols());
                    }
                    return this.functionSymbols = ImmutableCreator.create(fs);
                }
            }
        }
        return this.functionSymbols;
    }

    /**
     * Extracts all function symbols that occur at the root positions of LHS of
     * user-defined rules.
     * @return
     */
    public ImmutableSet<IFunctionSymbol<?>> getRootSymbols() {
        if (this.rootSymbols == null) {
            synchronized (this) {
                if (this.rootSymbols == null) {
                    final Set<IFunctionSymbol<?>> fs =
                        new LinkedHashSet<IFunctionSymbol<?>>();
                    for (final IRule rule : this.rules) {
                        fs.add(rule.getRootSymbol());
                    }
                    return this.rootSymbols = ImmutableCreator.create(fs);
                }
            }
        }
        return this.functionSymbols;
    }

    /**
     * Extracts all variables that occur in the user-defined rules.
     * @return
     */
    public ImmutableSet<IVariable<?>> getVariables() {
        if (this.variables == null) {
            synchronized (this) {
                if (this.variables == null) {
                    final Set<IVariable<?>> vars = new LinkedHashSet<IVariable<?>>();
                    for (final IRule rule : this.rules) {
                        vars.addAll(rule.getVariables());
                    }
                    return this.variables = ImmutableCreator.create(vars);
                }
            }
        }
        return this.variables;
    }

    /**
     * Determines the function symbols that are defined by the user-defined
     * rules.
     * @return
     */
    public ImmutableSet<IFunctionSymbol<?>> getDefinedSymbols() {
        return this.getRootSymbols();
    }

    /**
     * @return true iff fs is a constructor
     */
    public Boolean isConstructor(final IFunctionSymbol<?> fs) {
        final ImmutableSet<IFunctionSymbol<?>> defined = this.getDefinedSymbols();
        if (defined.contains(fs)) {
            return false;
        }
        return fs.getSemantics() == null
            || PredefinedUtil.getPredefinedConstructor(fs) != null;
    }

    /**
     * Extracts the left hand sides of the user-defined user-defined rules.
     * @return
     */
    public ImmutableSet<IFunctionApplication<?>> getLeftHandSides() {
        if (this.leftHandSides == null) {
            synchronized (this) {
                if (this.leftHandSides == null) {
                    final Set<IFunctionApplication<?>> lhss =
                        new LinkedHashSet<IFunctionApplication<?>>();
                    for (final IRule rule : this.rules) {
                        lhss.add(rule.getLeft());
                    }
                    return this.leftHandSides = ImmutableCreator.create(lhss);
                }
            }
        }
        return this.leftHandSides;
    }

    /**
     * Extracts the left hand sides of the user-defined rules in standard
     * representation.
     * @return
     */
    public ImmutableSet<IFunctionApplication<?>> getStandardLeftHandSides() {
        if (this.standardLeftHandSides == null) {
            synchronized (this) {
                if (this.standardLeftHandSides == null) {
                    final Set<IFunctionApplication<?>> lhss =
                        new LinkedHashSet<IFunctionApplication<?>>();
                    for (final R rule : this.rules) {
                        lhss.add(rule.getLhsInStandardRepresentation());
                    }
                    return this.standardLeftHandSides =
                        ImmutableCreator.create(lhss);
                }
            }
        }
        return this.standardLeftHandSides;
    }

    /**
     * Extracts the left hand sides of the user-defined rules and returns them
     * sorted by root symbols.
     */
    public ImmutableMap<IFunctionSymbol<?>, ImmutableSet<IFunctionApplication<?>>> getRootToStandardLeftHandSides() {
        if (this.rootToStandardLeftHandSides == null) {
            synchronized (this) {
                if (this.rootToStandardLeftHandSides == null) {
                    final Map<IFunctionSymbol<?>, Set<IFunctionApplication<?>>> tmp =
                        new LinkedHashMap<IFunctionSymbol<?>, Set<IFunctionApplication<?>>>();
                    for (final R rule : this.rules) {
                        final IFunctionSymbol<?> root =
                            rule.getLeft().getRootSymbol();
                        Set<IFunctionApplication<?>> lhss = tmp.get(root);
                        if (lhss == null) {
                            lhss = new LinkedHashSet<IFunctionApplication<?>>();
                            tmp.put(root, lhss);
                        }
                        lhss.add(rule.getLhsInStandardRepresentation());
                    }
                    final Map<IFunctionSymbol<?>, ImmutableSet<IFunctionApplication<?>>> tmpRootToStandardLeftHandSides =
                        new LinkedHashMap<IFunctionSymbol<?>, ImmutableSet<IFunctionApplication<?>>>();
                    for (final Map.Entry<IFunctionSymbol<?>, Set<IFunctionApplication<?>>> entry : tmp.entrySet()) {
                        tmpRootToStandardLeftHandSides.put(entry.getKey(),
                            ImmutableCreator.create(entry.getValue()));
                    }
                    return this.rootToStandardLeftHandSides =
                        ImmutableCreator.create(tmpRootToStandardLeftHandSides);
                }
            }
        }
        return this.rootToStandardLeftHandSides;
    }

    /**
     * Extracts the left hand sides of the user-defined rules that have a
     * specific function symbol as root.
     * @param rootSymbol - the root symbol
     * @return left hand sides of the user-defined rules that have the specified
     * root symbol.
     */
    public ImmutableSet<IFunctionApplication<?>> getStandardLeftHandSides(final IFunctionSymbol<?> rootSymbol) {
        final ImmutableSet<IFunctionApplication<?>> lhss =
            this.getRootToStandardLeftHandSides().get(rootSymbol);
        return lhss != null ? lhss : RuleAnalysis.EMPTY_FUNCTIONAPP_SET;
    }

    /**
     * Extracts the left hand sides of the user-defined rules and returns them
     * sorted by root symbols.
     */
    public ImmutableMap<IFunctionSymbol<?>, ImmutableSet<IFunctionApplication<?>>> getRootToLeftHandSides() {
        if (this.rootToLeftHandSides == null) {
            synchronized (this) {
                if (this.rootToLeftHandSides == null) {
                    final Map<IFunctionSymbol<?>, Set<IFunctionApplication<?>>> tmp =
                        new LinkedHashMap<IFunctionSymbol<?>, Set<IFunctionApplication<?>>>();
                    for (final R rule : this.rules) {
                        final IFunctionSymbol<?> root =
                            rule.getLeft().getRootSymbol();
                        Set<IFunctionApplication<?>> lhss = tmp.get(root);
                        if (lhss == null) {
                            lhss = new LinkedHashSet<IFunctionApplication<?>>();
                            tmp.put(root, lhss);
                        }
                        lhss.add(rule.getLeft());
                    }
                    final Map<IFunctionSymbol<?>, ImmutableSet<IFunctionApplication<?>>> tmpRootToLeftHandSides =
                        new LinkedHashMap<IFunctionSymbol<?>, ImmutableSet<IFunctionApplication<?>>>();
                    for (final Map.Entry<IFunctionSymbol<?>, Set<IFunctionApplication<?>>> entry : tmp.entrySet()) {
                        tmpRootToLeftHandSides.put(entry.getKey(),
                            ImmutableCreator.create(entry.getValue()));
                    }
                    return this.rootToLeftHandSides =
                        ImmutableCreator.create(tmpRootToLeftHandSides);
                }
            }
        }
        return this.rootToLeftHandSides;
    }

    /**
     * get R as a mapping from defined symbols to corresponding user-defined
     * rules
     */
    public ImmutableMap<IFunctionSymbol<?>, ImmutableSet<R>> getRuleMap() {
        if (this.ruleMap == null) {
            synchronized (this) {
                if (this.ruleMap == null) {
                    final Map<IFunctionSymbol<?>, Set<R>> tmp =
                        RuleAnalysis.generateRuleMap(this.rules);
                    final Map<IFunctionSymbol<?>, ImmutableSet<R>> ruleMap =
                        new LinkedHashMap<IFunctionSymbol<?>, ImmutableSet<R>>();
                    for (final Map.Entry<IFunctionSymbol<?>, Set<R>> entry : tmp.entrySet()) {
                        ruleMap.put(entry.getKey(),
                            ImmutableCreator.create(entry.getValue()));
                    }
                    return this.ruleMap = ImmutableCreator.create(ruleMap);
                }
            }
        }
        return this.ruleMap;
    }

    public static <R extends IRule> Map<IFunctionSymbol<?>, Set<R>> generateRuleMap(final Collection<R> rules) {
        final Map<IFunctionSymbol<?>, Set<R>> res =
            new LinkedHashMap<IFunctionSymbol<?>, Set<R>>();
        for (final R rule : rules) {
            final IFunctionSymbol<?> root = rule.getLeft().getRootSymbol();
            Set<R> rls = res.get(root);
            if (rls == null) {
                rls = new LinkedHashSet<R>();
                res.put(root, rls);
            }
            rls.add(rule);
        }
        return res;
    }

    /**
     * returns a map from defined symbols (of rhss) to corresponding
     * user-defined rules. Collapsing rules have null as "defined symbol".
     * @param rules
     */
    public ImmutableMap<IFunctionSymbol<?>, ImmutableSet<R>> getReversedRuleMap() {
        if (this.reverseRuleMap == null) {
            synchronized (this) {
                if (this.reverseRuleMap == null) {
                    final Map<IFunctionSymbol<?>, Set<R>> tmp =
                        new LinkedHashMap<IFunctionSymbol<?>, Set<R>>();
                    for (final R rule : this.rules) {
                        final ITerm<?> rhs = rule.getRight();
                        final IFunctionSymbol<?> f =
                            rhs.isVariable() ? null
                                : ((IFunctionApplication<?>) rhs).getRootSymbol();

                        Set<R> fRules = tmp.get(f);
                        if (fRules == null) {
                            fRules = new LinkedHashSet<R>();
                            tmp.put(f, fRules);
                        }
                        fRules.add(rule);
                    }
                    final Map<IFunctionSymbol<?>, ImmutableSet<R>> reverseRuleMap =
                        new LinkedHashMap<IFunctionSymbol<?>, ImmutableSet<R>>();
                    for (final Map.Entry<IFunctionSymbol<?>, Set<R>> entry : tmp.entrySet()) {
                        this.ruleMap.put(entry.getKey(),
                            ImmutableCreator.create(entry.getValue()));
                    }
                    return this.reverseRuleMap =
                        ImmutableCreator.create(reverseRuleMap);
                }
            }
        }
        return this.reverseRuleMap;
    }

    /**
     * Computes whether some of the given user-defined rules is collapsing
     */
    public boolean isCollapsing() {
        return this.getReversedRuleMap().containsKey(null);
    }

    /**
     * Extracts the left hand sides of the user-defined rules that have a
     * specific function symbol as root.
     * @param rootSymbol - the root symbol
     * @return left hand sides of the user-defined rules that have the specified
     * root symbol.
     */
    public ImmutableSet<IFunctionApplication<?>> getLeftHandSides(final IFunctionSymbol<?> rootSymbol) {
        final ImmutableSet<IFunctionApplication<?>> lhss =
            this.getRootToLeftHandSides().get(rootSymbol);
        return lhss != null ? lhss : RuleAnalysis.EMPTY_FUNCTIONAPP_SET;
    }

    /**
     * Extracts all terms used in the ruled.
     * @return all terms used in the ruled.
     */
    public Set<? extends ITerm<?>> getTerms() {
        if (this.terms == null) {
            synchronized (this) {
                if (this.terms == null) {
                    final Set<ITerm<?>> t = new LinkedHashSet<ITerm<?>>();
                    for (final R rule : this.rules) {
                        t.addAll(rule.getTerms());
                    }
                    return this.terms = ImmutableCreator.create(t);
                }
            }
        }
        return this.terms;
    }

    /**
     * Extract all domains used in a collection of user-defined rules.
     */
    public ImmutableSet<Domain> getDomains() {
        if (this.domains == null) {
            synchronized (this) {
                if (this.domains == null) {
                    final Set<PredefinedSemantics<?>> predefined =
                        this.getPredefinedFunctions();
                    final Set<Domain> d = new LinkedHashSet<Domain>();
                    for (final PredefinedSemantics<?> sem : predefined) {
                        if (!sem.isConstructor()) {
                            final PredefinedFunction<?, ?> func =
                                (PredefinedFunction<?, ?>) sem;
                            d.addAll(func.getDomains());
                            d.add(func.getResultDomain());
                        }
                    }
                    final Domain z = DomainFactory.INTEGERS;
                    this.unrestricted = d.contains(z);
                    this.restricted = false;
                    for (final Domain dom : d) {
                        if (dom instanceof IntegerDomain) {
                            if (((IntegerDomain<?>) dom).getBits() != 0) {
                                this.restricted = true;
                                break;
                            }
                        }
                    }
                    return this.domains = ImmutableCreator.create(d);
                }
            }
        }
        return this.domains;
    }

    /**
     * Get critical pairs for all rules
     */
    public CriticalPairs getCriticalPairs() {
        return this.getCriticalPairs(this.rules);
    }

    public CriticalPairs getCriticalPairs(final ImmutableSet<R> rules) {
        if (Globals.useAssertions) {
            assert rules == this.rules || this.rules.containsAll(rules) : "rules must be a subset of the rules of this analysis.";
        }
        synchronized (this.criticalPairs) {
            CriticalPairs res = this.criticalPairs.get(rules);
            if (res == null) {
                res = new CriticalPairs(rules, this.getRuleMap());
                this.criticalPairs.put(rules, res);
            }
            return res;
        }
    }

    /**
     * Determines the dependency pairs for the user-defined rules.
     * @return all dependency pairs public ImmutableSet<UnconditionalIRule>
     * getDependencyPairs() { if (dependencyPairs == null) { synchronized(this)
     * { if (dependencyPairs == null) { final Set<HasName> used = new
     * LinkedHashSet<HasName>(getFunctionSymbols());
     * used.addAll(getVariables()); dpFreshNames = new FreshNameGenerator(used,
     * FreshNameGenerator.DEPENDENCY_PAIRS); dpSymbolToFreshSymbol = new
     * LinkedHashMap<IFunctionSymbol<?>, IFunctionSymbol<?>>(); final
     * Set<UnconditionalIRule> d = new LinkedHashSet<UnconditionalIRule>();
     * final ImmutableSet<IFunctionSymbol<?>> defined = getDefinedSymbols(); for
     * (final R rule : rules) { if (!rule.getRight().isVariable()) { // generate
     * fresh symbol for lhs final IFunctionApplication<?> left = rule.getLeft();
     * IFunctionApplication<?> dpLhs = null; for (final ITerm<?> t :
     * rule.getRight().getNonVariableSubTerms()) { if (!left.hasProperSubterm(t)
     * && defined.contains(((IFunctionApplication<?>)t).getRootSymbol())) { if
     * (dpLhs == null) { // create fresh function symbol for dp lhs dpLhs = new
     * IFunctionApplication<?>(getFreshDpSymbol(left.getRootSymbol()),
     * left.getArguments()); } // generate fresh function symbol for rhs
     * IFunctionApplication<?> rhs = (IFunctionApplication<?>)t; rhs = new
     * IFunctionApplication<?>(getFreshDpSymbol(rhs.getRootSymbol()),
     * rhs.getArguments()); d.add(IRuleFactory.create(dpLhs, rhs)); } } } }
     * return dependencyPairs = ImmutableCreator.create(d); } } } return
     * dependencyPairs; } private IFunctionSymbol<?> getFreshDpSymbol(final
     * IFunctionSymbol<?> symbol) { if (Globals.useAssertions) { assert
     * symbol.getSemantics() == null :
     * "do not create DP symbols for pre-defined function symbols"; }
     * IFunctionSymbol<?> res = dpSymbolToFreshSymbol.get(symbol); if (res == null)
     * { res =
     * IFunctionSymbol.create(dpFreshNames.getFreshName(symbol.getName(),
     * false), symbol.getSemantics()); dpSymbolToFreshSymbol.put(symbol, res); }
     * return res; }
     */

    public ImmutableSet<PredefinedSemantics<?>> getPredefinedFunctions() {
        if (this.predefinedFunctions == null) {
            synchronized (this) {
                if (this.predefinedFunctions == null) {
                    final ImmutableSet<IFunctionSymbol<?>> symbols =
                        this.getFunctionSymbols();
                    final Set<PredefinedSemantics<?>> funcs =
                        new LinkedHashSet<PredefinedSemantics<?>>();

                    boolean bw = false;
                    boolean predefDefSym = false;

                    for (final IFunctionSymbol<?> sym : symbols) {
                        final PredefinedSemantics<?> sem = sym.getSemantics();
                        if (sem != null) {
                            funcs.add(sem);
                            if (!sem.isConstructor()) {
                                predefDefSym = true;
                                bw |= ((PredefinedFunction<?, ?>) sem).isBitwise();
                            }
                        }
                    }

                    this.bitwise = bw;
                    this.predefinedDefSymbols = predefDefSym;

                    return this.predefinedFunctions =
                        ImmutableCreator.create(funcs);
                }
            }
        }
        return this.predefinedFunctions;
    }

    /**
     * Checks if unrestricted integers occur in the rules.
     */
    public boolean hasUnrestrictedInt() {
        // this.unrestricted is calculated on first getDomains() invocation
        if (this.domains == null) {
            this.getDomains();
        }
        return this.unrestricted;
    }

    /**
     * Checks if the rules satisfy the variable condition.
     */
    public boolean satVarCondition() {
        if (this.satVarCondition == null) {
            synchronized (this) {
                if (this.satVarCondition == null) {
                    this.satVarCondition = true;
                    for (final R rule : this.rules) {
                        if (!rule.getLeft().getVariables().containsAll(
                            rule.getRight().getVariables())) {
                            this.satVarCondition = false;
                            break;
                        }
                    }
                    return this.satVarCondition;
                }
            }
        }
        return this.satVarCondition;
    }

    /**
     * Checks if restricted integers occur in the rules.
     */
    public boolean hasRestrictedInt() {
        // this.restricted is calculated on first getDomains() invocation
        if (this.domains == null) {
            this.getDomains();
        }
        return this.restricted;
    }

    /**
     * Checks if bitwise operations occur in the rules.
     */
    public boolean hasBitwiseOps() {
        if (this.predefinedFunctions == null) {
            this.getPredefinedFunctions();
        }
        return this.bitwise;
    }

    /**
     * Checks if defined predefined symbols (sic!) occur in the rules.
     */
    public boolean hasPredefinedDefSymbols() {
        if (this.predefinedFunctions == null) {
            this.getPredefinedFunctions();
        }
        return this.predefinedDefSymbols;
    }

//    public FunctionAnalysis getFunctionAnalysis(final IFunctionSymbol<?> fs) {
//        synchronized (functionAnalysis) {
//            FunctionAnalysis res = functionAnalysis.get(fs);
//            if (res == null) {
//                final ImmutableSet<R> rulesForFs = getRuleMap().get(fs);
//                boolean isConstant = true;
//                final Map<Integer, RelDependency> dependencies =
//                    new LinkedHashMap<Integer, RelDependency>();
//                final Set<Integer> projectionPos = new LinkedHashSet<Integer>();
//                final Set<ImmutablePair<ImmutableSet<Integer>, Boolean>> posCombinations =
//                    new LinkedHashSet<ImmutablePair<ImmutableSet<Integer>, Boolean>>();
//                if (rulesForFs != null) {
//                    for (final R rule : rulesForFs) {
//                        final ITerm<?> right = rule.getRight();
//                        final Set<IVariable<?>> variables = right.getVariables();
//                        if (!variables.isEmpty()) {
//                            // compute var positions
//                            final Map<IVariable<?>, ImmutableSet<Integer>> varPos =
//                                new LinkedHashMap<IVariable<?>, ImmutableSet<Integer>>();
//                            final int arity = fs.getArity();
//                            final ArrayList<Set<IVariable<?>>> posToVar =
//                                new ArrayList<Set<IVariable<?>>>(arity);
//                            for (final ITerm<?> leftArg : rule.getLeft().getArguments()) {
//                                posToVar.add(leftArg.getVariables());
//                            }
//                            final Set<Integer> consideredPositions =
//                                new LinkedHashSet<Integer>();
//                            for (final IVariable<?> var : variables) {
//                                final Set<Integer> positions =
//                                    new LinkedHashSet<Integer>();
//                                for (int i = arity - 1; i >= 0; i--) {
//                                    if (posToVar.get(i).contains(var)) {
//                                        positions.add(i);
//                                        consideredPositions.add(i);
//                                    }
//                                }
//                                varPos.put(var,
//                                    ImmutableCreator.create(positions));
//                            }
//
//                            isConstant = false;
//                            if (variables.size() == 1) {
//                                projectionPos.addAll(consideredPositions);
//                            }
//
//                            final Set<ITerm<?>> arithSubTerms =
//                                getMaxArithSubterms(right);
//                            for (final ITerm<?> arithSub : arithSubTerms) {
//                                final Set<IVariable<?>> arithVars =
//                                    arithSub.getVariables();
//                                // compute arith movement
//                                if (arithVars.size() == 1
//                                    && arithSub.getVariableCount().values().iterator().next() == 1) {
//                                    final BigInteger arithDir =
//                                        getArithDirection(arithSub);
//                                    RelDependency dir;
//                                    if (arithDir == null) {
//                                        dir = RelDependency.Wild;
//                                    } else {
//                                        switch (arithDir.signum()) {
//                                        case 0:
//                                            dir = RelDependency.Independent;
//                                            break;
//                                        case 1:
//                                            dir = RelDependency.Increasing;
//                                            break;
//                                        case -1:
//                                            dir = RelDependency.Decreasing;
//                                            break;
//                                        default:
//                                            dir = RelDependency.Wild;
//                                        }
//                                    }
//                                    for (final IVariable<?> arithVar : arithVars) {
//                                        for (final Integer i : varPos.get(arithVar)) {
//                                            dependencies.put(i, addDependency(
//                                                dependencies.get(i), dir));
//                                        }
//                                    }
//                                } else {
//                                    for (final IVariable<?> arithVar : arithVars) {
//                                        for (final Integer i : varPos.get(arithVar)) {
//                                            dependencies.put(i,
//                                                RelDependency.Wild);
//                                        }
//                                    }
//                                }
//                            }
//                        }
//                    }
//                }
//                res =
//                    new FunctionAnalysis(fs, isConstant,
//                        ImmutableCreator.create(dependencies),
//                        ImmutableCreator.create(projectionPos),
//                        ImmutableCreator.create(posCombinations));
//                functionAnalysis.put(fs, res);
//            }
//            return res;
//        }
//    }
//
//    protected RelDependency addDependency(final RelDependency current,
//        final RelDependency add) {
//        if (current == null) {
//            return add;
//        } else if (current == RelDependency.Wild || add == RelDependency.Wild) {
//            return RelDependency.Wild;
//        } else if (current == RelDependency.Independent) {
//            return add;
//        } else if (add == RelDependency.Independent) {
//            return current;
//        } else if (current != add) {
//            return RelDependency.Wild;
//        } else {
//            return current;
//        }
//    }
//
//    protected Set<ITerm<?>> getMaxArithSubterms(final ITerm<?> term) {
//        if (term.isVariable()) {
//            return java.util.Collections.<ITerm<?>> emptySet();
//        } else {
//            final IFunctionApplication<?> fa = (IFunctionApplication<?>) term;
//            final IFunctionSymbol<?> fs = fa.getRootSymbol();
//            final PredefinedFunction<?, ?> func =
//                PredefinedUtil.getPredefinedFunction(fs);
//            if (func != null && func.isArithmetic()) {
//                return java.util.Collections.<ITerm<?>>singleton(term);
//            }
//            final Set<ITerm<?>> res = new LinkedHashSet<ITerm<?>>();
//            for (final ITerm<?> arg : fa.getArguments()) {
//                res.addAll(getMaxArithSubterms(arg));
//            }
//            return res;
//        }
//    }

//    protected <R extends IntRing<R>> BigInteger getArithDirection(final ITerm<R> t) {
//        if (t.isVariable()) {
//            return BigInteger.ZERO;
//        }
//        final IFunctionApplication<?> fa = (IFunctionApplication<?>) t;
//        final IFunctionSymbol<?> fs = fa.getRootSymbol();
//        final BigInt pfInt =
//            PredefinedUtil.getIntValue(fs, DomainFactory.INTEGERS);
//        if (pfInt != null) {
//            return pfInt.getBigInt();
//        }
//        boolean isAdd = false;
//        final PredefinedFunction<?, ?> func =
//            PredefinedUtil.getPredefinedFunction(fs);
//        if (func != null) {
//            if (func.getFunc() == Func.Add) {
//                isAdd = true;
//            } else {
//                if (func.getFunc() == Func.Sub) {
//                    isAdd = false;
//                } else {
//                    return null;
//                }
//            }
//        } else {
//            return null;
//        }
//        BigInteger sum = BigInteger.ZERO;
//        for (int i = 0; i < 2; i++) {
//            final BigInteger argDir = getArithDirection(fa.getArgument(i));
//            if (argDir == null) {
//                return null;
//            } else {
//                if (isAdd || i == 0) {
//                    sum = sum.add(argDir);
//                } else {
//                    sum = sum.subtract(argDir);
//                }
//            }
//        }
//        return sum;
//    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result =
            prime * result
                + ((this.predefinedMap == null) ? 0 : this.predefinedMap.hashCode());
        result = prime * result + ((this.rules == null) ? 0 : this.rules.hashCode());
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final RuleAnalysis<?> other = (RuleAnalysis<?>) obj;
        if (this.predefinedMap == null) {
            if (other.predefinedMap != null) {
                return false;
            }
        } else if (!this.predefinedMap.equals(other.predefinedMap)) {
            return false;
        }
        if (this.rules == null) {
            if (other.rules != null) {
                return false;
            }
        } else if (!this.rules.equals(other.rules)) {
            return false;
        }
        return true;
    }

    @Override
    public final String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public final String export(final Export_Util o) {
        return this.export(o, IDPExportable.DEFAULT_LEVEL);
    }

    @Override
    public final String export(final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        final StringBuilder sb = new StringBuilder();
        this.export(sb, o, verbosityLevel);
        return sb.toString();
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        sb.append(o.set(this.rules, Export_Util.NICE_SET));
    }


}
