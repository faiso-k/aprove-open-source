package aprove.verification.dpframework.DPProblem.TheoremProver;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public class RuleTransformation {
    /*
     * attributes
     */
    private ImmutableSet<Rule>      usableRules             = null;
    private ImmutableSet<Rule>      strictDecreasing        = null;
    private ImmutableList<TRSTerm>     dpArguments             = null;
    private MonotonicityConstraints monotonicityConstraints = null;
    private SortCalculator          sortCalculator          = null;
    private TRSFunctionApplication     myTrue                  = null;
    private TRSFunctionApplication     myFalse                 = null;
    private FunctionSymbol          myOr                    = null;
    private NameManager nameManager;

    /*
     * public methods
     */

    public ImmutableList<TRSTerm> getTransformedDPArguments() {
        return this.dpArguments;
    }

    public RuleTransformation(ImmutableSet<Rule> usableRules, ImmutableSet<Rule> strictDecreasing, ImmutableArrayList<TRSTerm> dpArguments,
            MonotonicityConstraints monotonicityConstraints, SortCalculator sortCalculator,
            NameManager nameManager) {
        this.usableRules = usableRules;
        this.strictDecreasing = strictDecreasing;
        this.dpArguments = dpArguments;
        this.monotonicityConstraints = monotonicityConstraints;
        this.sortCalculator = sortCalculator;

        this.myTrue = nameManager.getTrueApp();
        this.myFalse = nameManager.getFalseApp();
        this.myOr = nameManager.getOrSym();
        this.nameManager = nameManager;
    }

    /**
     * Initializes RuleTransformation object.
     *
     * @param R
     * @param P
     * @param argumentFiltering
     * @return initialized RuleTransformation object.
     */
    public static RuleTransformation create(ImmutableSet<Rule> usableRules, ImmutableSet<Rule> strictDecreasing,
            ImmutableArrayList<TRSTerm> dpArguments, MonotonicityConstraints monotonicityConstraints,
            SortCalculator sortCalculator, NameManager nameManager) {
        return new RuleTransformation(usableRules, strictDecreasing, dpArguments,
                monotonicityConstraints, sortCalculator, nameManager);
    }

    public ImmutableSet<Rule> applyChainRuleTransformation() {
        RuleAnalysis<Rule> analysis = new RuleAnalysis<Rule>(this.strictDecreasing, IDPPredefinedMap.EMPTY_MAP);

        ImmutableSet<FunctionSymbol> callingFunctions = this.computeCallingFunctions(this.usableRules, analysis.getDefinedSymbols());

        Map<FunctionSymbol, FunctionSymbol> transformedFunctionSymbols = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();

        analysis = new RuleAnalysis<Rule>(this.usableRules, IDPPredefinedMap.EMPTY_MAP);
        for (FunctionSymbol callingFunction : callingFunctions) {
            String namePrime = this.nameManager.getFreshName(callingFunction.getName() + '\'');
            FunctionSymbol callingFunctionPrime = FunctionSymbol.create(namePrime, callingFunction.getArity());
            transformedFunctionSymbols.put(callingFunction, callingFunctionPrime);
            this.sortCalculator.addDefFunctionSymbolToMaps(callingFunctionPrime, this.sortCalculator.getFunInputSortMap().get(
                    callingFunction), this.sortCalculator.getBool());
        }

        ImmutableMap<FunctionSymbol, FunctionSymbol> immutabletransformedFunctionSymbols = ImmutableCreator
                .create(transformedFunctionSymbols);

        // Transform DP arguments needed for formula

        List<TRSTerm> transformedDPArgs = new ArrayList<TRSTerm>();
        for (TRSTerm arg : this.dpArguments) {
            if (!arg.isVariable()) {
                TRSFunctionApplication funApp = this.eliminateFalse(this.derive((TRSFunctionApplication) arg, callingFunctions,
                        this.monotonicityConstraints, immutabletransformedFunctionSymbols));

                Map<TRSVariable, List<Position>> vars = funApp.getVariablePositions();
                for (Entry<TRSVariable, List<Position>> entry : vars.entrySet()) {
                    if (this.sortCalculator.getVariableSortMap().get(entry.getKey()) == null) {
                        for (Position pos : entry.getValue()) {
                            int argNo = pos.lastIndex();
                            pos = pos.shorten(1);
                            TRSFunctionApplication f = (TRSFunctionApplication) funApp.getSubterm(pos);
                            this.sortCalculator.addVariableToMap(entry.getKey(), this.sortCalculator.getFunInputSortMap().get(
                                    f.getRootSymbol()).get(argNo));
                            break;
                        }
                    }
                }
                transformedDPArgs.add(funApp);
            }
        }
        this.dpArguments = ImmutableCreator.create(transformedDPArgs);

        // Transform rules
        Set<Rule> newRules = new LinkedHashSet<Rule>();
        for (Rule rule : this.usableRules) {
            Rule newRule = null;
            if (this.strictDecreasing.contains(rule)) {
                newRule = Rule.create(TRSTerm.createFunctionApplication(transformedFunctionSymbols.get(rule.getLeft()
                        .getRootSymbol()), rule.getLeft().getArguments()), this.myTrue);
                newRules.add(newRule);
            }
            else if (callingFunctions.contains(rule.getRootSymbol())) {
                newRule = Rule.create(TRSTerm.createFunctionApplication(transformedFunctionSymbols.get(rule.getLeft()
                        .getRootSymbol()), rule.getLeft().getArguments()), this.eliminateFalse(this.derive(rule.getRight(), callingFunctions,
                        this.monotonicityConstraints, immutabletransformedFunctionSymbols)));
                newRules.add(newRule);
            }
        }
        newRules.addAll(this.usableRules);

        return ImmutableCreator.create(newRules);
    }

    /*
     * private methods
     */

    private TRSFunctionApplication eliminateFalse(TRSFunctionApplication input) {
        if (input.getRootSymbol().equals(this.myOr)) {
            if (input.getArgument(0).equals(this.myFalse)) {
                return this.eliminateFalse((TRSFunctionApplication) input.getArgument(1));
            }
            else if (input.getArgument(1).equals(this.myFalse)) {
                return this.eliminateFalse((TRSFunctionApplication) input.getArgument(0));
            }
            else {
                ArrayList<TRSFunctionApplication> args = new ArrayList<TRSFunctionApplication>();
                args.add(this.eliminateFalse((TRSFunctionApplication) input.getArgument(0)));
                args.add(this.eliminateFalse((TRSFunctionApplication) input.getArgument(1)));
                return TRSTerm.createFunctionApplication(this.myOr, ImmutableCreator.create(args));
            }
        }
        else {
            return input;
        }
    }

    private ImmutableSet<FunctionSymbol> computeCallingFunctions(ImmutableSet<Rule> usableRules,
            ImmutableSet<FunctionSymbol> strictFunctions) {

        Set<FunctionSymbol> callingFunctions = new LinkedHashSet<FunctionSymbol>(strictFunctions);
        boolean funSymAdded;
        do {
            funSymAdded = false;
            for (Rule rule : usableRules) {
                Set<FunctionSymbol> rightFunSyms = rule.getRight().getFunctionSymbols();
                rightFunSyms.retainAll(callingFunctions);
                if (!rightFunSyms.isEmpty()) {
                    if (!callingFunctions.contains(rule.getLeft().getRootSymbol())) {
                        funSymAdded = true;
                    }
                    callingFunctions.add(rule.getLeft().getRootSymbol());
                }
            }
        }
        while (funSymAdded);
        return ImmutableCreator.create(callingFunctions);
    }

    private TRSFunctionApplication derive(TRSTerm input, ImmutableSet<FunctionSymbol> callingFunctions, MonotonicityConstraints mu,
            ImmutableMap<FunctionSymbol, FunctionSymbol> transformedFunctionSymbols) {
        Set<FunctionSymbol> inputFunctionSymbols = input.getFunctionSymbols();
        inputFunctionSymbols.retainAll(callingFunctions);
        // First case of derive function
        if (inputFunctionSymbols.isEmpty() || input.isVariable()) {
            return this.myFalse;
        }
        // Second case of derive function
        TRSFunctionApplication funApp = (TRSFunctionApplication) input;
        FunctionSymbol root = funApp.getRootSymbol();
        TRSFunctionApplication transformedfunApp = null;
        if (callingFunctions.contains(root) && mu.getConstraint(root).isEmpty()) {
            return TRSTerm.createFunctionApplication(transformedFunctionSymbols.get(root), funApp.getArguments());
        }
        // Third case of derive function
        if (!callingFunctions.contains(root)) {
            transformedfunApp = this.myFalse;
        }
        else {
            transformedfunApp = TRSTerm.createFunctionApplication(transformedFunctionSymbols.get(root), funApp.getArguments());
        }
        // Third and fourth case of the derive function
        for (Integer arg : mu.getConstraint(root)) {
            if (!funApp.getArgument(arg).isVariable()) {
                ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                args.add(transformedfunApp);
                args.add(this.derive(funApp.getArgument(arg), callingFunctions, mu, transformedFunctionSymbols));
                transformedfunApp = TRSTerm.createFunctionApplication(this.myOr, ImmutableCreator.create(args));
            }
        }
        return transformedfunApp;
    }
}
