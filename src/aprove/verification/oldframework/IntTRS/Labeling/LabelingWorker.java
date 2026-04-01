package aprove.verification.oldframework.IntTRS.Labeling;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.Labeling.LabelingProcessor.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Matthias Hoelzel, Marc Brockschmidt
 */
public class LabelingWorker {
    /** Set of the old rules. */
    private final Set<IGeneralizedRule> oldRules;

    /** Set of resulting rules. */
    private Set<IGeneralizedRule> resultRules;

    /** Set of defined symbols */
    private Set<FunctionSymbol> symbols;

    /** Stores the maximal arity of the symbols */
    private int maxArity;

    /** Set of symbol names. */
    private Set<String> symbolsNames;

    /** The given processor arguments */
    private final Arguments arguments;

    /** Collects the right arguments. */
    private LinkedHashMap<Pair<FunctionSymbol, Integer>, LinkedHashSet<TRSTerm>> rightArgumentsMap;

    /** Position to be transformed. */
    private Pair<FunctionSymbol, Integer> workingIndex;

    /** New function symbols used for the case analysis */
    private LinkedHashMap<TRSTerm, FunctionSymbol> newSymbolsMap;

    /** Generates fresh names. */
    private final FreshNameGenerator ng;

    /** The proof we are going to create. */
    private final LabelingProof proof;

    /**
     * Constructor.
     * @param prob the input problem
     * @param args some processor arguments
     * @param gen some name generator
     */
    public LabelingWorker(
        final Set<IGeneralizedRule> rules,
        final Arguments args,
        final FreshNameGenerator gen,
        final LabelingProof labelingProof)
    {
        this.oldRules = rules;
        this.arguments = args;
        this.ng = gen;
        this.proof = labelingProof;
    }

    /**
     * Performs some labeling actions.
     * @return set of rules
     */
    public Set<IGeneralizedRule> work() {
        // 1. Find defined symbols
        this.findDefinedSymbols();

        // 2. Find relevant information
        this.findRelevantInformation();

        // 3. Introduce new symbols and produce the new rules
        this.createResultRules();

        // 4. Return result ;)
        return this.resultRules;
    }

    /**
     * Finds the defined symbols to avoid name conflicts.
     */
    private void findDefinedSymbols() {
        this.symbolsNames = new LinkedHashSet<>(this.oldRules.size());
        this.symbols = new LinkedHashSet<>(this.oldRules.size());
        this.maxArity = 0;

        for (final IGeneralizedRule rule : this.oldRules) {
            final FunctionSymbol currentSymbol = rule.getLeft().getRootSymbol();
            this.symbols.add(currentSymbol);
            this.symbols.add(((TRSFunctionApplication) rule.getRight()).getRootSymbol());
            this.maxArity = (this.maxArity < currentSymbol.getArity()) ? (currentSymbol.getArity()) : (this.maxArity);

            this.symbolsNames.add(rule.getLeft().getRootSymbol().getName());
            this.symbolsNames.add(((TRSFunctionApplication) rule.getRight()).getName());
        }
    }

    /**
     * Finds relevant information.
     */
    private void findRelevantInformation() {
        // At the moment we only do this:
        this.collectRightArguments();
        this.filterRightArguments();
    }

    /**
     * Collects the arguments occurring at the right side.
     */
    private void collectRightArguments() {
        // Store for each function symbol
        // and each position which constants occur at the right side.
        this.rightArgumentsMap = new LinkedHashMap<>(this.maxArity * this.symbols.size());

        for (final IGeneralizedRule rule : this.oldRules) {
            final TRSFunctionApplication rightFunc = (TRSFunctionApplication) rule.getRight();
            final FunctionSymbol rightSymbol = rightFunc.getRootSymbol();

            for (int i = 0; i < rightFunc.getArguments().size(); i++) {
                final TRSTerm arg = rightFunc.getArgument(i);

                final Pair<FunctionSymbol, Integer> indexPair = new Pair<FunctionSymbol, Integer>(rightSymbol, i);

                if (this.rightArgumentsMap.get(indexPair) == null) {
                    this.rightArgumentsMap.put(indexPair, new LinkedHashSet<TRSTerm>());
                }

                this.rightArgumentsMap.get(indexPair).add(arg);
            }
        }
    }

    /**
     * Filters the collection of right arguments to those that are usable for
     * our purposes.
     */
    private void filterRightArguments() {
        this.workingIndex = null;
        search: for (final Pair<FunctionSymbol, Integer> index : this.rightArgumentsMap.keySet()) {
            final Set<TRSTerm> arguments = this.rightArgumentsMap.get(index);

            int numberOfConstants = 0;
            for (final TRSTerm arg : arguments) {
                if (!arg.isConstant()) {
                    continue search;
                } else {
                    numberOfConstants++;
                }
            }

            if (numberOfConstants <= this.arguments.maxNumberOfCases && numberOfConstants > 1) {
                this.workingIndex = index;
                break;
            }
        }
    }

    /**
     * Creates the new rules.
     */
    private void createResultRules() {
        this.createNewRules();
    }

    /**
     * Creates the new rules by replacing the right sides.
     */
    private void createNewRules() {
        if (this.workingIndex == null) {
            this.resultRules = null;
        } else {
            this.generateNewSymbols();
            this.proof.fillInformation(
                this.workingIndex,
                this.rightArgumentsMap.get(this.workingIndex),
                this.newSymbolsMap);

            this.resultRules =
                new LinkedHashSet<>(this.oldRules.size() * this.rightArgumentsMap.get(this.workingIndex).size());
            for (final IGeneralizedRule rule : this.oldRules) {
                this.generateOutputRules(rule);
            }
        }
    }

    /**
     * Invents fresh symbol names for the new rules.
     */
    private void generateNewSymbols() {
        final int arity = this.workingIndex.x.getArity();
        this.newSymbolsMap = new LinkedHashMap<>(this.rightArgumentsMap.get(this.workingIndex).size());
        for (final TRSTerm arg : this.rightArgumentsMap.get(this.workingIndex)) {
            this.newSymbolsMap.put(arg, FunctionSymbol.create(this.generateNewSymbolName(), arity));
        }
    }

    /**
     * Returns a unused symbol name.
     * @return a string
     */
    private String generateNewSymbolName() {
        String candidate;
        do {
            candidate = this.ng.getFreshName("f", false);
        } while (this.symbolsNames.contains(candidate));
        return candidate;
    }

    /**
     * Generate the new rules which are needed to simulate the current rule.
     * @param currentRule some old rule to be considered
     */
    private void generateOutputRules(final IGeneralizedRule currentRule) {
        final TRSFunctionApplication leftSide = currentRule.getLeft();
        final TRSFunctionApplication rightSide = (TRSFunctionApplication) currentRule.getRight();
        final TRSTerm condition = currentRule.getCondTerm();
        // The new left sides and the new condition are build simultaneously
        // in order to avoid confusion ;)
        final LinkedHashSet<Pair<TRSFunctionApplication, TRSTerm>> newLeftSidesAndConds;
        if (leftSide.getRootSymbol().equals(this.workingIndex.x)) {
            newLeftSidesAndConds = new LinkedHashSet<>(this.rightArgumentsMap.get(this.workingIndex).size());
            // For every new argument we create a new left side:
            final ImmutableList<TRSTerm> leftArguments = leftSide.getArguments();
            for (final TRSTerm argument : this.rightArgumentsMap.get(this.workingIndex)) {
                final TRSFunctionApplication newLeftSide =
                    TRSTerm.createFunctionApplication(this.newSymbolsMap.get(argument), leftArguments);
                // and the new condition:
                final TRSVariable v = (TRSVariable) leftArguments.get(this.workingIndex.y);
                final TRSTerm newCondition =
                    ToolBox.buildAnd(condition == null ? ToolBox.buildTrue() : condition, ToolBox.buildEq(v, argument));
                newLeftSidesAndConds.add(new Pair<TRSFunctionApplication, TRSTerm>(newLeftSide, newCondition));
            }
        } else {
            newLeftSidesAndConds = new LinkedHashSet<>(1);
            newLeftSidesAndConds.add(new Pair<TRSFunctionApplication, TRSTerm>(leftSide, condition));
        }
        // Prepare the right side:
        final TRSFunctionApplication newRightSide;
        if (rightSide.getRootSymbol().equals(this.workingIndex.x)) {
            final ImmutableList<TRSTerm> rightArguments = rightSide.getArguments();
            final TRSTerm constantArgument = rightArguments.get(this.workingIndex.y);
            assert (
                constantArgument.isConstant()
                && this.rightArgumentsMap.get(this.workingIndex).contains(constantArgument)
            );
            final FunctionSymbol newRightSymbol = this.newSymbolsMap.get(constantArgument);
            newRightSide = TRSTerm.createFunctionApplication(newRightSymbol, rightArguments);
        } else {
            newRightSide = rightSide;
        }
        // And now we just compose everything:
        for (final Pair<TRSFunctionApplication, TRSTerm> leftAndCond : newLeftSidesAndConds) {
            this.resultRules.add(IGeneralizedRule.create(leftAndCond.x, newRightSide, leftAndCond.y));
        }
    }
}
