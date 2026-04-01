/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.utility;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * This class provides methods to analyze sets of rules. Generated once all values are cached.
 * @author mpluecke
 *
 */
public class RuleAnalysis<R extends GeneralizedRule> implements Immutable, HasTRSTerms {

    public static <Q extends GeneralizedRule> RuleAnalysis<Q> emptyAnalysis() {
        return new RuleAnalysis<Q>(ImmutableCreator.create(java.util.Collections.<Q>emptySet()), IDPPredefinedMap.EMPTY_MAP);
    }

    private final ImmutableSet<R> rules;
    private final IDPPredefinedMap predefinedMap;
    private volatile ImmutableSet<FunctionSymbol> rootSymbols;
    private volatile ImmutableSet<FunctionSymbol> functionSymbols;
    private volatile ImmutableSet<TRSVariable> variables;
    private volatile ImmutableSet<PredefinedSemantics> predefinedFunctions;
    private volatile ImmutableSet<TRSFunctionApplication> leftHandSides;
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<TRSFunctionApplication>> rootToLeftHandSides;
    private volatile ImmutableSet<TRSTerm> terms;
    private volatile ImmutableSet<FunctionSymbol> definedSymbols;
    private volatile ImmutableSet<Domain> domains;
    private volatile ImmutableSet<GeneralizedRule> dependencyPairs;
    private volatile FreshNameGenerator dpFreshNames;
    private volatile Map<FunctionSymbol, FunctionSymbol> dpSymbolToFreshSymbol;
    private volatile ImmutableSet<TRSFunctionApplication> standardLeftHandSides;
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<TRSFunctionApplication>> rootToStandardLeftHandSides;
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<R>> ruleMap;
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<R>> reverseRuleMap;
    private volatile Map<ImmutableSet<R>, CriticalPairs> criticalPairs;
    private volatile Boolean satVarCondition;
    private final Map<FunctionSymbol, FunctionAnalysis> functionAnalysis;

    /**
     * R set contains restricted integers.
     *
     * (computed by getDomains)
     */
    private boolean restricted;

    /**
     * R set contains unrestricted integers.
     *
     * (computed by getDomains)
     */
    private boolean unrestricted;

    /**
     * R set contains bitwise predefined functions.
     *
     * (computed by getPredefinedFunctions)
     */
    private boolean bitwise;

    /**
     * R set contains predefined defined functions
     * (as opposed to integer or boolean constants
     * as predefined symbols only)
     *
     * (computed by getPredefinedFunctions)
     */
    private boolean predefinedDefSymbols;


    public RuleAnalysis (ImmutableSet<R> rules, IDPPredefinedMap predefinedMap) {
        this.rules = rules;
        this.predefinedMap = predefinedMap;
        this.functionAnalysis = new LinkedHashMap<FunctionSymbol, FunctionAnalysis>();
        this.criticalPairs = new LinkedHashMap<ImmutableSet<R>, CriticalPairs>();
    }

    /**
     * Returns the rules that are analyzed.
     */
    public ImmutableSet<R> getRules() {
        return this.rules;
    }

    /**
     * return the map op pre defined function symbols
     */
    public IDPPredefinedMap getPreDefinedMap() {
        return this.predefinedMap;
    }

    /**
     * Extracts all function symbols that occur in the rules.
     * @return the set of function symbols that occur in the rules.
     */
    public ImmutableSet<FunctionSymbol> getFunctionSymbols() {
        if (this.functionSymbols == null) {
            synchronized(this) {
                if (this.functionSymbols == null) {
                    return this.functionSymbols = ImmutableCreator.create(CollectionUtils.getFunctionSymbols(this.rules));
                }
            }
        }
        return this.functionSymbols;
    }

    /**
     * Extracts all function symbols that occur at the root positions of LHS.
     * @return the set of function symbols that occur in the rules.
     */
    public ImmutableSet<FunctionSymbol> getRootSymbols() {
        if (this.rootSymbols == null) {
            synchronized(this) {
                if (this.rootSymbols == null) {
                    return this.rootSymbols = ImmutableCreator.create(CollectionUtils.getRootSymbols(this.rules));
                }
            }
        }
        return this.rootSymbols;
    }

    /**
     * Extracts all variables that occur in the rules. Just wraps {@see Collections#getFunctionSymbols}.
     * @return the set of variables that occur in the rules.
     */
    @SuppressWarnings("unchecked")
    public ImmutableSet<TRSVariable> getVariables() {
        if (this.variables == null) {
            synchronized(this) {
                if (this.variables == null) {
                    return
                        this.variables =
                            ImmutableCreator.create((Set<TRSVariable>)CollectionUtils.getVariables(this.rules));
                }
            }
        }
        return this.variables;
    }

    /**
     * Determines the function symbols that are defined by the rules.
     * @return the set of function symbols that are defined.
     */
    public ImmutableSet<FunctionSymbol> getDefinedSymbols() {
        if (this.definedSymbols == null) {
            synchronized(this) {
                if (this.definedSymbols == null) {
                    return this.definedSymbols = ImmutableCreator.create(CollectionUtils.getRootSymbols(this.rules));
                }
            }
        }
        return this.definedSymbols;
    }

    /**
     * @return true iff fs is a constructor
     */
    public Boolean isConstructor(FunctionSymbol fs) {
        ImmutableSet<FunctionSymbol> defined = this.getDefinedSymbols();
        if (defined.contains(fs)) {
            return false;
        }
        return this.predefinedMap.getPredefinedSemantics(fs) == null;
    }

    /**
     * Extracts the left hand sides of the rules. Just wraps {@see Collections#getLeftHandSides}.
     * @return left hand sides of the rules.
     */
    public ImmutableSet<TRSFunctionApplication> getLeftHandSides() {
        if (this.leftHandSides == null) {
            synchronized(this) {
                if (this.leftHandSides == null) {
                    return this.leftHandSides = ImmutableCreator.create(CollectionUtils.getLeftHandSides(this.rules));
                }
            }
        }
        return this.leftHandSides;
    }

    /**
     * Extracts the left hand sides of the rules in standard representation.
     * @return left hand sides of the rules.
     */
    public ImmutableSet<TRSFunctionApplication> getStandardLeftHandSides () {
        if (this.standardLeftHandSides == null) {
            synchronized(this) {
                if (this.standardLeftHandSides == null) {
                    Set<TRSFunctionApplication> lhss = new LinkedHashSet<TRSFunctionApplication>();
                    for (R rule : this.rules) {
                        lhss.add(rule.getLhsInStandardRepresentation());
                    }
                    return this.standardLeftHandSides = ImmutableCreator.create(lhss);
                }
            }
        }
        return this.standardLeftHandSides;
    }

    /**
     * Extracts the left hand sides of the rules and returns them sorted by root symbols.
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<TRSFunctionApplication>> getRootToStandardLeftHandSides() {
        if (this.rootToStandardLeftHandSides == null) {
            synchronized(this) {
                if (this.rootToStandardLeftHandSides == null) {
                    Map<FunctionSymbol, Set<TRSFunctionApplication>> tmp = new LinkedHashMap<FunctionSymbol, Set<TRSFunctionApplication>>();
                    for (R rule : this.rules) {
                        FunctionSymbol root = rule.getLeft().getRootSymbol();
                        Set<TRSFunctionApplication> lhss = tmp.get(root);
                        if (lhss == null) {
                            lhss = new LinkedHashSet<TRSFunctionApplication>();
                            tmp.put(root, lhss);
                        }
                        lhss.add(rule.getLhsInStandardRepresentation());
                    }
                    Map<FunctionSymbol, ImmutableSet<TRSFunctionApplication>> tmpRootToStandardLeftHandSides = new LinkedHashMap<FunctionSymbol, ImmutableSet<TRSFunctionApplication>>();
                    for (Map.Entry<FunctionSymbol, Set<TRSFunctionApplication>> entry : tmp.entrySet()) {
                        tmpRootToStandardLeftHandSides.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
                    }
                    return this.rootToStandardLeftHandSides = ImmutableCreator.create(tmpRootToStandardLeftHandSides);
                }
            }
        }
        return this.rootToStandardLeftHandSides;
    }

    /**
    * Extracts the left hand sides of the rules that have a specific function symbol as root.
    * @param rootSymbol - the root symbol
    * @return left hand sides of the rules that have the specified root symbol.
    */
   public ImmutableSet<TRSFunctionApplication> getStandardLeftHandSides(FunctionSymbol rootSymbol) {
       ImmutableSet<TRSFunctionApplication> lhss = this.getRootToStandardLeftHandSides().get(rootSymbol);
       return lhss != null ? lhss : IDPUtility.EMPTY_FUNCTIONAPP_SET;
   }

    /**
     * Extracts the left hand sides of the rules and returns them sorted by root symbols.
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<TRSFunctionApplication>> getRootToLeftHandSides() {
        if (this.rootToLeftHandSides == null) {
            synchronized(this) {
                if (this.rootToLeftHandSides == null) {
                    Map<FunctionSymbol, Set<TRSFunctionApplication>> tmp = new LinkedHashMap<FunctionSymbol, Set<TRSFunctionApplication>>();
                    for (R rule : this.rules) {
                        FunctionSymbol root = rule.getLeft().getRootSymbol();
                        Set<TRSFunctionApplication> lhss = tmp.get(root);
                        if (lhss == null) {
                            lhss = new LinkedHashSet<TRSFunctionApplication>();
                            tmp.put(root, lhss);
                        }
                        lhss.add(rule.getLeft());
                    }
                    Map<FunctionSymbol, ImmutableSet<TRSFunctionApplication>> tmpRootToLeftHandSides = new LinkedHashMap<FunctionSymbol, ImmutableSet<TRSFunctionApplication>>();
                    for (Map.Entry<FunctionSymbol, Set<TRSFunctionApplication>> entry : tmp.entrySet()) {
                        tmpRootToLeftHandSides.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
                    }
                    return this.rootToLeftHandSides = ImmutableCreator.create(tmpRootToLeftHandSides);
                }
            }
        }
        return this.rootToLeftHandSides;
    }

    /**
     * get R as a mapping from defined symbols to corresponding rules
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<R>> getRuleMap() {
        if (this.ruleMap == null) {
            synchronized(this) {
                if (this.ruleMap == null) {
                    Map<FunctionSymbol, Set<R>> tmp = new LinkedHashMap<FunctionSymbol, Set<R>> ();
                    for (R rule : this.rules) {
                        FunctionSymbol root = rule.getLeft().getRootSymbol();
                        Set<R> rules = tmp.get(root);
                        if (rules == null) {
                            rules = new LinkedHashSet<R>();
                            tmp.put(root, rules);
                        }
                        rules.add(rule);
                    }
                    Map<FunctionSymbol, ImmutableSet<R>> ruleMap = new LinkedHashMap<FunctionSymbol, ImmutableSet<R>>();
                    for (Map.Entry<FunctionSymbol, Set<R>> entry : tmp.entrySet()) {
                        ruleMap.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
                    }
                    return this.ruleMap = ImmutableCreator.create(ruleMap);
                }
            }
        }
        return this.ruleMap;
    }

    /**
     * returns a map from defined symbols (of rhss) to corresponding rules. Collapsing rules
     * have null as "defined symbol".
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<R>> getReversedRuleMap() {
        if (this.reverseRuleMap == null) {
            synchronized(this) {
                if (this.reverseRuleMap == null) {
                    Map<FunctionSymbol, Set<R>> tmp = new LinkedHashMap<FunctionSymbol, Set<R>>();
                    for (R rule : this.rules) {
                        TRSTerm rhs = rule.getRight();
                        FunctionSymbol f = rhs.isVariable() ? null : ((TRSFunctionApplication) rhs).getRootSymbol();

                        Set<R> fRules = tmp.get(f);
                        if (fRules == null) {
                            fRules = new LinkedHashSet<R>();
                            tmp.put(f, fRules);
                        }
                        fRules.add(rule);
                    }
                    Map<FunctionSymbol, ImmutableSet<R>>  reverseRuleMap = new LinkedHashMap<FunctionSymbol, ImmutableSet<R>>();
                    for (Map.Entry<FunctionSymbol, Set<R>> entry : tmp.entrySet()) {
                        this.ruleMap.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
                    }
                    return this.reverseRuleMap = ImmutableCreator.create(reverseRuleMap);
                }
            }
        }
        return this.reverseRuleMap;
    }


    /**
     * Computes whether some of the given rules is collapsing
     */
    public boolean isCollapsing() {
         return this.getReversedRuleMap().containsKey(null);
     }


    /**
    * Extracts the left hand sides of the rules that have a specific function symbol as root.
    * @param rootSymbol - the root symbol
    * @return left hand sides of the rules that have the specified root symbol.
    */
   public ImmutableSet<TRSFunctionApplication> getLeftHandSides(FunctionSymbol rootSymbol) {
       ImmutableSet<TRSFunctionApplication> lhss = this.getRootToLeftHandSides().get(rootSymbol);
       return lhss != null ? lhss : IDPUtility.EMPTY_FUNCTIONAPP_SET;
   }


    /**
     * Extracts all terms used in the ruled.
     * @return all terms used in the ruled.
     */
    @Override
    public Set<? extends TRSTerm> getTerms() {
        if (this.terms == null) {
            synchronized(this) {
                if (this.terms == null) {
                    Set<TRSTerm> t = new LinkedHashSet<TRSTerm>();
                    for (R rule : this.rules) {
                        t.addAll(rule.getTerms());
                    }
                    return this.terms = ImmutableCreator.create(t);
                }
            }
        }
        return this.terms;
    }

    /**
     * Extract all domain suffixes used in a Collection of rules.
     */
    public ImmutableSet<Domain> getDomains() {
        if (this.domains == null) {
            synchronized(this) {
                if (this.domains == null) {
                    Set<PredefinedSemantics> predefined = this.getPredefinedFunctions();
                    Set<Domain> d = new LinkedHashSet<Domain>();
                    for (PredefinedSemantics sem : predefined) {
                        if (sem.isFunction()) {
                            d.addAll(((PredefinedFunction<? extends Domain>)sem).getDomains());
                        }
                    }

                    Domain z = DomainFactory.INTEGERS;
                    this.unrestricted = d.contains(z);
                    this.restricted = false;
                    for (Domain dom : d) {
                        if (dom instanceof IntegerDomain) {
                            if (((IntegerDomain) dom).getBits() != 0) {
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


    public CriticalPairs getCriticalPairs(ImmutableSet<R> rules) {
        if (Globals.useAssertions) {
            assert rules == this.rules || this.rules.containsAll(rules) : "rules must be a subset of the rules of this analysis.";
        }
        synchronized(this.criticalPairs) {
            CriticalPairs res = this.criticalPairs.get(rules);
            if (res == null) {
                res = new CriticalPairs(rules, this.getRuleMap());
                this.criticalPairs.put(rules, res);
            }
            return res;
        }
    }


    /**
     * Determines the dependency pairs.
     * @return all dependency pairs
     */
    /**
     * Determines the dependency pairs.
     * @return all dependency pairs
     */
    public ImmutableSet<GeneralizedRule> getDependencyPairs() {
        if (this.dependencyPairs == null) {
            synchronized(this) {
                if (this.dependencyPairs == null) {
                    Set<HasName> used = new LinkedHashSet<HasName>(this.getFunctionSymbols());
                    used.addAll(this.getVariables());
                    this.dpFreshNames = new FreshNameGenerator(used, FreshNameGenerator.DEPENDENCY_PAIRS);
                    this.dpSymbolToFreshSymbol = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();
                    Set<GeneralizedRule> d = new LinkedHashSet<GeneralizedRule>();
                    ImmutableSet<FunctionSymbol> defined = this.getDefinedSymbols();
                    for (R rule : this.rules) {
                        if (!rule.getRight().isVariable()) {
                            // generate fresh symbol for lhs
                            TRSFunctionApplication left = rule.getLeft();
                            TRSFunctionApplication dpLhs = null;
                            for (TRSTerm t : rule.getRight().getNonVariableSubTerms()) {
                                if (!left.hasProperSubterm(t) && defined.contains(((TRSFunctionApplication)t).getRootSymbol())) {
                                    if (dpLhs == null) {
                                        // create fresh function symbol for dp lhs
                                        dpLhs =
                                            TRSTerm.createFunctionApplication(
                                                this.getFreshDpSymbol(left.getRootSymbol()),
                                                left.getArguments()
                                            );
                                    }
                                    // generate fresh function symbol for rhs
                                    TRSFunctionApplication rhs = (TRSFunctionApplication)t;
                                    rhs =
                                        TRSTerm.createFunctionApplication(
                                            this.getFreshDpSymbol(rhs.getRootSymbol()),
                                            rhs.getArguments()
                                        );
                                    d.add(GeneralizedRule.create(dpLhs, rhs));
                                }
                            }
                        }
                    }
                    return this.dependencyPairs = ImmutableCreator.create(d);
                }
            }
        }
        return this.dependencyPairs;
    }

    private FunctionSymbol getFreshDpSymbol(FunctionSymbol symbol) {
        FunctionSymbol res = this.dpSymbolToFreshSymbol.get(symbol);
        if (res == null) {
            res = FunctionSymbol.create(this.dpFreshNames.getFreshName(symbol.getName(), false), symbol.getArity());
            this.dpSymbolToFreshSymbol.put(symbol, res);
        }
        return res;
    }

    public ImmutableSet<PredefinedSemantics> getPredefinedFunctions() {
        if (this.predefinedFunctions == null) {
            synchronized(this) {
                if (this.predefinedFunctions == null) {
                    ImmutableSet<FunctionSymbol> symbols = this.getFunctionSymbols();
                    Set<PredefinedSemantics> funcs = new LinkedHashSet<PredefinedSemantics>();

                    boolean bw = false;
                    boolean predefDefSym = false;

                    for (FunctionSymbol sym : symbols) {
                        PredefinedSemantics sem = this.predefinedMap.getPredefinedSemantics(sym);
                        if (sem != null) {
                            funcs.add(sem);
                            if (sem.isFunction()) {
                                predefDefSym = true;
                                bw |= ((PredefinedFunction<? extends Domain>)sem).isBitwise();
                            }
                        }
                    }

                    this.bitwise = bw;
                    this.predefinedDefSymbols = predefDefSym;

                    return this.predefinedFunctions = ImmutableCreator.create(funcs);
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
                    for (R rule : this.rules) {
                        if (!rule.getLeft().getVariables().containsAll(rule.getRight().getVariables())) {
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


    public FunctionAnalysis getFunctionAnalysis(FunctionSymbol fs) {
        synchronized(this.functionAnalysis) {
            FunctionAnalysis res = this.functionAnalysis.get(fs);
            if (res == null) {
                ImmutableSet<R> rulesForFs = this.getRuleMap().get(fs);
                boolean isConstant = true;
                Map<Integer, RelDependency> dependencies = new LinkedHashMap<Integer, RelDependency>();
                Set<Integer> projectionPos = new LinkedHashSet<Integer>();
                Set<ImmutablePair<ImmutableSet<Integer>, Boolean>> posCombinations = new LinkedHashSet<ImmutablePair<ImmutableSet<Integer>, Boolean>>();
                if (rulesForFs != null) {
                    for (R rule : rulesForFs) {
                        TRSTerm right = rule.getRight();
                        Set<TRSVariable> variables = right.getVariables();
                        if (!variables.isEmpty()) {
                            // compute var positions
                            Map<TRSVariable, ImmutableSet<Integer>> varPos = new LinkedHashMap<TRSVariable, ImmutableSet<Integer>>();
                            int arity = fs.getArity();
                            ArrayList<Set<TRSVariable>> posToVar = new ArrayList<Set<TRSVariable>>(arity);
                            for (TRSTerm leftArg : rule.getLeft().getArguments()) {
                                posToVar.add(leftArg.getVariables());
                            }
                            Set<Integer> consideredPositions = new LinkedHashSet<Integer>();
                            for (TRSVariable var : variables) {
                                Set<Integer> positions = new LinkedHashSet<Integer>();
                                for (int i = arity - 1; i>=0; i--) {
                                    if (posToVar.get(i).contains(var)) {
                                        positions.add(i);
                                        consideredPositions.add(i);
                                    }
                                }
                                varPos.put(var, ImmutableCreator.create(positions));
                            }


                            isConstant = false;
                            if (variables.size() == 1) {
                                projectionPos.addAll(consideredPositions);
                            }

                            Set<TRSTerm> arithSubTerms = this.getMaxArithSubterms(right);
                            for (TRSTerm arithSub : arithSubTerms) {
                                Set<TRSVariable> arithVars = arithSub.getVariables();
                                // compute arith movement
                                if (arithVars.size() == 1 && arithSub.getVariableCount().values().iterator().next() == 1) {
                                    BigInteger arithDir = this.getArithDirection(arithSub);
                                    RelDependency dir;
                                    if (arithDir == null) {
                                        dir = RelDependency.Wild;
                                    } else {
                                        switch (arithDir.signum()) {
                                        case 0 :
                                            dir = RelDependency.Independent;
                                            break;
                                        case 1:
                                            dir = RelDependency.Increasing;
                                            break;
                                        case -1:
                                            dir = RelDependency.Decreasing;
                                            break;
                                        default :
                                            dir = RelDependency.Wild;
                                        }
                                    }
                                    for (TRSVariable arithVar : arithVars) {
                                        for (Integer i : varPos.get(arithVar)) {
                                            dependencies.put(i, this.addDependency(dependencies.get(i), dir));
                                        }
                                    }
                                } else {
                                    for (TRSVariable arithVar : arithVars) {
                                        for (Integer i : varPos.get(arithVar)) {
                                            dependencies.put(i, RelDependency.Wild);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                res = new FunctionAnalysis(fs, isConstant, ImmutableCreator.create(dependencies), ImmutableCreator.create(projectionPos), ImmutableCreator.create(posCombinations));
                this.functionAnalysis.put(fs, res);
            }
            return res;
        }
    }

    protected RelDependency addDependency(RelDependency current, RelDependency add) {
        if (current == null) {
            return add;
        } else if (current == RelDependency.Wild || add == RelDependency.Wild) {
            return RelDependency.Wild;
        } else if (current == RelDependency.Independent) {
            return add;
        } else if (add == RelDependency.Independent) {
            return current;
        } else if (current != add) {
            return RelDependency.Wild;
        } else {
            return current;
        }
    }

    protected Set<TRSTerm> getMaxArithSubterms(TRSTerm term) {
        if (term.isVariable()) {
            return java.util.Collections.<TRSTerm>emptySet();
        } else {
            TRSFunctionApplication fa = (TRSFunctionApplication) term;
            FunctionSymbol fs = fa.getRootSymbol();
            PredefinedFunction<? extends Domain> func = this.predefinedMap.getPredefinedFunction(fs);
            if (func != null && func.isArithmetic()) {
                return java.util.Collections.singleton(term);
            }
            Set<TRSTerm> res = new LinkedHashSet<TRSTerm>();
            for (TRSTerm arg : fa.getArguments()) {
                res.addAll(this.getMaxArithSubterms(arg));
            }
            return res;
        }
    }

    protected BigInteger getArithDirection(TRSTerm t) {
        if (t.isVariable()) {
            return BigInteger.ZERO;
        }
        TRSFunctionApplication fa = (TRSFunctionApplication) t;
        FunctionSymbol fs = fa.getRootSymbol();
        BigInteger pfInt = this.predefinedMap.getInt(fs, DomainFactory.INTEGERS);
        if (pfInt != null) {
            return pfInt;
        }
        boolean isAdd = false;
        PredefinedFunction<? extends Domain> func = this.predefinedMap.getPredefinedFunction(fs);
        if (func != null) {
            if (func.getFunc() == Func.Add) {
                isAdd = true;
            } else {
                if (func.getFunc() == Func.Sub) {
                    isAdd = false;
                } else {
                    return null;
                }
            }
        } else {
            return null;
        }
        BigInteger sum = BigInteger.ZERO;
        for (int i = 0; i < 2; i++) {
            BigInteger argDir = this.getArithDirection(fa.getArgument(i));
            if (argDir == null) {
                return null;
            } else {
                if (isAdd || i == 0) {
                    sum = sum.add(argDir);
                } else {
                    sum = sum.subtract(argDir);
                }
            }
        }
        return sum;
    }

}
