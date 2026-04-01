package aprove.verification.oldframework.IntTRS.BoundedInts;

import java.util.*;
import java.util.Map.*;

import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.IntTRS.BoundedInts.BoundedIntTRSToIntTRSProcessor.Arguments;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.TerminationGraph.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Transforms a bounded integer rewrite system into a normal one.
 * @author Matthias Hoelzel
 */
public class BoundedRuleTransformer {
    /** Current form of the input rule. */
    private IGeneralizedRule current;

    /** What we know about the variables. */
    private final LinkedHashMap<TRSVariable, IntegerType> currentBounds;

    /** Output rules! */
    private final LinkedHashSet<IGeneralizedRule> outputRules;

    /** The rule before normalizations steps are performed. */
    private IGeneralizedRule startRule;

    /**
     * If we "inline" the normalization steps, then we obtain a set of
     * startRules instead.
     */
    private LinkedList<IGeneralizedRule> startRules;

    /** These rules perform the normalization steps. */
    private LinkedList<IGeneralizedRule> normalizationRules;

    /** This rule signalizes, that the values are in the correct domain. */
    private IGeneralizedRule endRule;

    /** SMT Solver */
    private YicesEngine smtEngine;

    /** Formula factory! */
    private FormulaFactory<SMTLIBTheoryAtom> factory;

    /** Given processor arguments. */
    private final Arguments arguments;

    /** Some aborter */
    private final Abortion aborter;

    /** Generates fresh names! */
    private final FreshNameGenerator ng;

    /**
     * Constructor!
     * @param input some IGeneralizedRule.
     * @param bounds some information about the ranges
     * @param args processor arguments
     * @param gen some name generator
     * @param abortion some aborter
     */
    public BoundedRuleTransformer(final IGeneralizedRule input, final Map<TRSVariable, IntegerType> bounds,
            final Arguments args, final FreshNameGenerator gen, final Abortion abortion) {
        this.current = input;
        this.outputRules = new LinkedHashSet<IGeneralizedRule>();
        this.currentBounds =
            bounds == null ? new LinkedHashMap<TRSVariable, IntegerType>() : new LinkedHashMap<TRSVariable, IntegerType>(
                bounds);
        this.arguments = args;
        this.ng = gen;
        this.aborter = abortion;
    }

    /**
     * Returns the output rules!
     * @return set of rules
     * @throws AbortionException can be aborted
     */
    public LinkedHashSet<IGeneralizedRule> getOutput() throws AbortionException {
        if (this.outputRules.isEmpty()) {
            this.generateOutputRules();
        }
        return this.outputRules;
    }

    /**
     * Generates the output rules!
     * @throws AbortionException can be aborted
     */
    private void generateOutputRules() throws AbortionException {
        // Contains remaining inner casts like CAST_32(x+17*CAST_64(18*CAST_32(19*(y+x))))
        // or casts occurring in the condition term?
        if (this.containsCastsAtWrongPositions()) {
            // Reformulate casts at wrong positions by creating more rules:
            this.reformulateCasts();
        } else {
            // Add range constraints:
            this.addRangeConstraints();

            // Generate normalization rules:
            this.generateNormalizationRules();

            // Remove unneeded rules:
            this.removeUnneededRules();

            // Put the rules together to generate output system:
            this.fillInOutputRules();
        }
    }

    /**
     * Checks for casts at wrong positions!
     * @return true, iff we found some.
     */
    private boolean containsCastsAtWrongPositions() {
        final TRSFunctionApplication rightSide = (TRSFunctionApplication) this.current.getRight();
        for (final TRSTerm arg : rightSide.getArguments()) {
            if (!this.checkTerm(arg)) {
                return false;
            }
        }
        return BoundedSymbolFactory.containsCastSymbol(this.current.getCondTerm());
    }

    /**
     * Checks whether or not the argument contains cast only at valid positions.
     * @param arg some term
     * @return boolean
     */
    private boolean checkTerm(final TRSTerm arg) {
        if (arg.isVariable()) {
            return true;
        } else {
            final TRSFunctionApplication func = (TRSFunctionApplication) arg;
            for (final TRSTerm argArg : func.getArguments()) {
                if (BoundedSymbolFactory.containsCastSymbol(argArg)) {
                    return false;
                }
            }
            return true;
        }
    }

    /**
     * Removes nested casts by introducing new variables. The original semantic
     * is maintained by the transformed condition.
     * @throws AbortionException can be aborted
     */
    private void reformulateCasts() throws AbortionException {
        // 1. Collect inner casts:
        final LinkedHashMap<TRSTerm, TRSVariable> toBeEvaluatedFirst = new LinkedHashMap<>();
        final TRSFunctionApplication oldRight = (TRSFunctionApplication) this.current.getRight();
        final ImmutableList<TRSTerm> args = oldRight.getArguments();
        final List<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
        for (final TRSTerm arg : args) {
            if (!arg.isVariable()) {
                final TRSFunctionApplication funcArg = (TRSFunctionApplication) arg;
                final ImmutableList<TRSTerm> argArgs = funcArg.getArguments();
                final List<TRSTerm> newArgArgs = new ArrayList<>(argArgs.size());
                for (final TRSTerm argArg : argArgs) {
                    newArgArgs.add(this.collectInnerCasts(argArg, toBeEvaluatedFirst));
                }
                newArgs.add(TRSTerm.createFunctionApplication(funcArg.getRootSymbol(), newArgArgs));
            } else {
                newArgs.add(arg);
            }
        }
        final TRSFunctionApplication newRight =
            TRSTerm.createFunctionApplication(oldRight.getRootSymbol(), newArgs);

        // 2. Collect cast at the constraint:
        final LinkedList<TRSTerm> castFormulas = new LinkedList<>();
        final LinkedList<TRSTerm> nonCastFormulas = new LinkedList<>();
        this.splitFormula(this.current.getCondTerm(), castFormulas, nonCastFormulas);

        final LinkedList<TRSTerm> filteredCastFormula = new LinkedList<>();
        for (final TRSTerm castForm : castFormulas) {
            filteredCastFormula.add(this.collectInnerCasts(castForm, toBeEvaluatedFirst));
        }

        // 3. Construct new rules:
        // 3.1 New auxiliary symbol
        final String newAuxiliarySymbolName = this.ng.getFreshName("aux", false);
        final int arity = this.current.getLeft().getRootSymbol().getArity() + toBeEvaluatedFirst.size();
        final FunctionSymbol auxiliarySymbol = FunctionSymbol.create(newAuxiliarySymbolName, arity);

        // 3.2 Fill in arguments
        final ArrayList<TRSTerm> newRightSide = new ArrayList<>(arity);
        final ArrayList<TRSVariable> newLeftSide = new ArrayList<>(arity);
        for (final TRSTerm leftVar : this.current.getLeft().getArguments()) {
            assert leftVar instanceof TRSVariable;
            newRightSide.add(leftVar);
            newLeftSide.add((TRSVariable) leftVar);
        }
        for (final Entry<TRSTerm, TRSVariable> e : toBeEvaluatedFirst.entrySet()) {
            newLeftSide.add(e.getValue());
            newRightSide.add(e.getKey());
        }

        // 3.3 Construct the new formula:
        final TRSTerm nonCastFormula = ToolBox.buildAnd(nonCastFormulas);
        final TRSTerm reformFormula = ToolBox.buildAnd(nonCastFormula, ToolBox.buildAnd(filteredCastFormula));

        // 3.4 Put everything together and obtain new rules:
        final LinkedList<IGeneralizedRule> reformRules = new LinkedList<>();
        reformRules.add(IGeneralizedRule.create(this.current.getLeft(),
            TRSTerm.createFunctionApplication(auxiliarySymbol, newRightSide), nonCastFormula));
        reformRules.add(IGeneralizedRule.create(
            TRSTerm.createFunctionApplication(auxiliarySymbol, newLeftSide), newRight, reformFormula));

        // Solve recursively:
        this.solveReformulatedRules(reformRules);
    }

    /**
     * Finds the atomic formulas and puts each of them either in castFormula, if
     * some cast-operation occurs, or otherwise in nonCastFormula
     * @param formula input formula
     * @param castFormula list of formulas with cast-symbols (to be filled)
     * @param nonCastFormula list of formulas without cast-symbols (to be
     * filled)
     */
    private void splitFormula(final TRSTerm formula,
        final LinkedList<TRSTerm> castFormula,
        final LinkedList<TRSTerm> nonCastFormula) {
        if (formula.isVariable()) {
            assert false : "Condition is variable?: " + formula;
        } else if (formula.isConstant()) {
            nonCastFormula.add(formula);
        } else {
            final TRSFunctionApplication funcFormula = (TRSFunctionApplication) formula;
            final FunctionSymbol sym = funcFormula.getRootSymbol();
            if (IDPPredefinedMap.DEFAULT_MAP.isLor(sym) || IDPPredefinedMap.DEFAULT_MAP.isLnot(sym)) {
                assert false : "Condition strange symbol: " + sym;
            } else {
                if (IDPPredefinedMap.DEFAULT_MAP.isLand(sym)) {
                    for (final TRSTerm arg : funcFormula.getArguments()) {
                        this.splitFormula(arg, castFormula, nonCastFormula);
                    }
                } else {
                    assert IDPPredefinedMap.DEFAULT_MAP.isPredefined(sym) : "Expected some predefined symbol, "
                        + "but found " + sym;
                    if (BoundedSymbolFactory.containsCastSymbol(funcFormula)) {
                        castFormula.add(funcFormula);
                    } else {
                        nonCastFormula.add(funcFormula);
                    }
                }
            }
        }
    }

    /**
     * Collects terms at wrong positions.
     * @param term current term
     * @param toBeEvaluatedFirst collects terms (and variable) that have to be
     * evaluated first
     * @return cleaned term
     */
    private TRSTerm collectInnerCasts(final TRSTerm term, final LinkedHashMap<TRSTerm, TRSVariable> toBeEvaluatedFirst) {
        if (term.isVariable()) {
            return term;
        } else {
            final TRSFunctionApplication func = (TRSFunctionApplication) term;
            final FunctionSymbol sym = func.getRootSymbol();
            if (BoundedSymbolFactory.isCastSymbol(sym)) {
                return this.addInvalidCast(func, toBeEvaluatedFirst);
            } else {
                final ImmutableList<TRSTerm> args = func.getArguments();
                final List<TRSTerm> newArgs = new ArrayList<>(args.size());
                for (final TRSTerm arg : args) {
                    newArgs.add(this.collectInnerCasts(arg, toBeEvaluatedFirst));
                }
                return TRSTerm.createFunctionApplication(sym, newArgs);
            }
        }

    }

    /**
     * Adds a term to be collection of term, that have to be evaluated first.
     * @param term some cast at wrong position
     * @param toBeEvaluatedFirst collection
     * @return Variable to use instead
     */
    private TRSVariable addInvalidCast(final TRSFunctionApplication term,
        final LinkedHashMap<TRSTerm, TRSVariable> toBeEvaluatedFirst) {
        if (toBeEvaluatedFirst.containsKey(term)) {
            return toBeEvaluatedFirst.get(term);
        } else {
            final TRSVariable newVar = TRSTerm.createVariable(this.ng.getFreshName("x", false));
            toBeEvaluatedFirst.put(term, newVar);
            final FunctionSymbol castSymbol = term.getRootSymbol();
            this.currentBounds.put(newVar, BoundedSymbolFactory.getCorrespondingDomain(castSymbol));
            return newVar;
        }
    }

    /**
     * Solve the reformulated rules by using this transformer class recursively.
     * @param rules list of rules to be transformed
     * @throws AbortionException can be aborted
     */
    private void solveReformulatedRules(final LinkedList<IGeneralizedRule> rules) throws AbortionException {
        for (final IGeneralizedRule rule : rules) {
            final BoundedRuleTransformer brt =
                new BoundedRuleTransformer(rule, this.currentBounds, this.arguments, this.ng, this.aborter);
            this.outputRules.addAll(brt.getOutput());
        }
    }

    /**
     * Adds constraints arising from the domain information of the variables.
     */
    private void addRangeConstraints() {
        final Set<TRSVariable> nonCondVariables = this.current.getVariables();
        final Set<TRSVariable> condVariables = this.current.getCondVariables();
        final LinkedHashSet<TRSVariable> variables = new LinkedHashSet<>(nonCondVariables.size() + condVariables.size());
        variables.addAll(nonCondVariables);
        variables.addAll(condVariables);

        TRSTerm condition = this.current.getCondTerm();
        for (final TRSVariable v : variables) {
            final IntegerType bd = this.currentBounds.get(v);
            if (bd == null) {
                continue;
            }
            condition = ToolBox.buildAnd(condition, ToolBox.buildLe(v, ToolBox.buildInt(bd.getUpper().getConstant())));
            condition = ToolBox.buildAnd(condition, ToolBox.buildGe(v, ToolBox.buildInt(bd.getLower().getConstant())));
        }

        this.current = IGeneralizedRule.create(this.current.getLeft(), this.current.getRight(), condition);
    }

    /**
     * Generates the required normalization rules. In case that the number of
     * required normalization steps can be anticipated, we apply these steps
     * directly.
     */
    private void generateNormalizationRules() {
        this.normalizationRules = new LinkedList<>();

        final TRSFunctionApplication rightSide = (TRSFunctionApplication) this.current.getRight();
        final int arity = rightSide.getRootSymbol().getArity();
        final ArrayList<TRSTerm> nonCastArguments = new ArrayList<>(arity);

        // Generate auxiliary symbol:
        final String auxiliarySymbolName = this.ng.getFreshName("aux_norm", false);
        final FunctionSymbol auxiliarySymbol = FunctionSymbol.create(auxiliarySymbolName, arity);

        // Generate normalization rule & generate new names & the final condition:
        // currentArg: needed to know which argument will be normalized
        int currentArg = 0;
        // Some data structures to build the final rule:
        final ArrayList<TRSVariable> finalVars = new ArrayList<>(arity);
        final LinkedList<TRSTerm> finalConditions = new LinkedList<>();
        for (final TRSTerm arg : rightSide.getArguments()) {
            // Current variable for the final rule:
            final TRSVariable currentVar = TRSTerm.createVariable(this.ng.getFreshName("x", false));
            finalVars.add(currentVar);

            if (arg instanceof TRSFunctionApplication
                && BoundedSymbolFactory.isCastSymbol(((TRSFunctionApplication) arg).getRootSymbol())) {
                final TRSFunctionApplication funcArg = (TRSFunctionApplication) arg;
                nonCastArguments.add(funcArg.getArgument(0));
                final IntegerType bd = BoundedSymbolFactory.getCorrespondingDomain(funcArg.getRootSymbol());

                // Create normalization rules:
                this.createNormalizationRules(auxiliarySymbol, currentArg, bd, this.normalizationRules);

                // Construct the "final" condition:
                finalConditions.add(ToolBox.buildLe(currentVar, ToolBox.buildInt(bd.getUpper().getConstant())));
                finalConditions.add(ToolBox.buildGe(currentVar, ToolBox.buildInt(bd.getLower().getConstant())));
            } else {
                // Nothing to normalize -> nothing to do!
                nonCastArguments.add(arg);
            }
            currentArg++;
        }

        // Build the start- & end-rule:
        this.startRule =
            IGeneralizedRule.create(this.current.getLeft(),
                TRSTerm.createFunctionApplication(auxiliarySymbol, nonCastArguments),
                this.current.getCondTerm());

        final TRSTerm finalCondition = ToolBox.buildAnd(finalConditions);
        final TRSFunctionApplication finalLeftSide =
            TRSTerm.createFunctionApplication(auxiliarySymbol, finalVars);
        final TRSFunctionApplication finalRightSide =
            TRSTerm.createFunctionApplication(rightSide.getRootSymbol(), finalVars);

        this.endRule = IGeneralizedRule.create(finalLeftSide, finalRightSide, finalCondition);
    }

    /**
     * Creates auxiliary rules for over-/underflow handling.
     * @param auxSymbol some auxiliary symbol
     * @param toCorrect current argument to be corrected
     * @param bd current domain
     * @param toInsert list to insert rules
     */
    private void createNormalizationRules(final FunctionSymbol auxSymbol,
        final int toCorrect,
        final IntegerType bd,
        final Collection<IGeneralizedRule> toInsert) {
        final int arity = auxSymbol.getArity();
        assert toCorrect >= 0 && toCorrect < arity;
        final ArrayList<TRSVariable> leftArgs = new ArrayList<>(arity);
        final ArrayList<TRSTerm> rightArgs1 = new ArrayList<>(arity);
        final ArrayList<TRSTerm> rightArgs2 = new ArrayList<>(arity);

        TRSTerm cond1 = null;
        TRSTerm cond2 = null;

        for (int i = 0; i < arity; i++) {
            final TRSVariable var = TRSTerm.createVariable(this.ng.getFreshName("x", false));

            leftArgs.add(var);
            if (i == toCorrect) {
                rightArgs1.add(TRSTerm.createFunctionApplication(
                    IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Add, DomainFactory.INTEGERS), var,
                    ToolBox.buildInt(bd.getNumberOfValues())));
                rightArgs2.add(TRSTerm.createFunctionApplication(
                    IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Sub, DomainFactory.INTEGERS), var,
                    ToolBox.buildInt(bd.getNumberOfValues())));

                cond1 = ToolBox.buildLt(var, ToolBox.buildInt(bd.getLower().getConstant()));
                cond2 = ToolBox.buildGt(var, ToolBox.buildInt(bd.getUpper().getConstant()));
            } else {
                rightArgs1.add(var);
                rightArgs2.add(var);
            }
        }

        assert cond1 != null && cond2 != null;

        final TRSFunctionApplication leftSide = TRSTerm.createFunctionApplication(auxSymbol, leftArgs);
        final IGeneralizedRule rule1 =
            IGeneralizedRule.create(leftSide, TRSTerm.createFunctionApplication(auxSymbol, rightArgs1),
                cond1);
        final IGeneralizedRule rule2 =
            IGeneralizedRule.create(leftSide, TRSTerm.createFunctionApplication(auxSymbol, rightArgs2),
                cond2);
        toInsert.add(rule1);
        toInsert.add(rule2);
    }

    /**
     * Removes rules, that are not reachable.
     * @throws AbortionException can be aborted
     */
    private void removeUnneededRules() throws AbortionException {
        // Prepare to inline the rule -> yields a list of start rules:
        this.startRules = new LinkedList<>();
        this.startRules.add(this.startRule);

        if (this.arguments.inlineLimit >= 0) {
            this.smtEngine = new YicesEngine();
            this.factory = new FullSharingFactory<SMTLIBTheoryAtom>();

            // We calculate the number of normalization steps, that
            // are possible after the usage of the initial rule. This will
            // be stored in the map "numberOfNormSteps".
            final LinkedHashMap<IGeneralizedRule, Integer> numberOfNormSteps = new LinkedHashMap<>();

            for (final IGeneralizedRule normRule : this.normalizationRules) {
                final Integer max = this.getMaxNumberOfNormalizationSteps(this.startRule, normRule);
                numberOfNormSteps.put(normRule, max);
            }

            // Now we can "inline" the normalization rules:
            final LinkedList<IGeneralizedRule> toBeRemoved = new LinkedList<>();
            for (final IGeneralizedRule normRule : this.normalizationRules) {
                final Integer maxNumberOfApplications = numberOfNormSteps.get(normRule);
                if (maxNumberOfApplications != null) {
                    final LinkedList<IGeneralizedRule> newStartRules = new LinkedList<>();
                    // Perform the normalization steps immediately:
                    for (final IGeneralizedRule currentStartRule : this.startRules) {
                        IGeneralizedRule newStartRule = currentStartRule;
                        for (int i = 0; i <= maxNumberOfApplications; i++) {
                            newStartRules.add(newStartRule);

                            // The next rule is only required, iff i is small enough:
                            if (i < maxNumberOfApplications) {
                                // Apply another normalization step:
                                newStartRule = (new Chaining(newStartRule, normRule, this.ng)).getResult();
                            }
                        }
                    }
                    this.startRules = newStartRules;
                    toBeRemoved.add(normRule);
                }
            }

            this.normalizationRules.removeAll(toBeRemoved);

            // If we get rid of all normalization rules, then we can just
            // chain the start rules together with the end-rule, so
            // in this case the end rule can be dropped, too.
            if (this.normalizationRules.isEmpty()) {
                final LinkedList<IGeneralizedRule> newStartRules = new LinkedList<>();
                for (final IGeneralizedRule oldStartRule : this.startRules) {
                    newStartRules.add(new Chaining(oldStartRule, this.endRule, this.ng).getResult());
                }
                this.startRules = newStartRules;
                // The end-rule is no longer needed:
                this.endRule = null;
            }
        }
    }

    /**
     * Calculates how many times a normalization rule might be used. Returns
     * null, if it can be used more often than a fixed limit.
     * @param currentStartRule the first ruls
     * @param normRule given normalization rule
     * @return Integer or null
     * @throws AbortionException can be aborted
     */
    private Integer getMaxNumberOfNormalizationSteps(final IGeneralizedRule currentStartRule,
        final IGeneralizedRule normRule) throws AbortionException {
        Integer result = 0;
        boolean unsat = true;

        IGeneralizedRule currentRule = currentStartRule;

        do {
            if (result > this.arguments.inlineLimit) {
                return null;
            }

            currentRule = (new Chaining(currentRule, normRule, this.ng)).getResult();
            assert currentRule != null;

            final LinkedList<Formula<SMTLIBTheoryAtom>> formulaList = new LinkedList<>();
            formulaList.add(ToolBox.boolTermToSMT_QF_IA(currentRule.getCondTerm(), this.factory, this.ng));
            YNM ynm;
            try {
                ynm = this.smtEngine.satisfiable(formulaList, SMTLogic.QF_LIA, this.aborter);
            } catch (final WrongLogicException e) {
                ynm = YNM.MAYBE;
                e.printStackTrace();
            }
            unsat = ynm.equals(YNM.NO);

            if (!unsat) {
                result++;
            }

        } while (!unsat);
        return result;
    }

    /**
     * Fills the field this.outputRules with some rules.
     * @throws AbortionException can be aborted
     */
    private void fillInOutputRules() throws AbortionException {
        final LinkedList<IGeneralizedRule> toAdd = new LinkedList<>();

        toAdd.addAll(this.startRules);
        toAdd.addAll(this.normalizationRules);

        if (this.endRule != null) {
            // The field endRule is reset to null, if this rule is not required.
            toAdd.add(this.endRule);
        }

        for (final IGeneralizedRule rule : toAdd) {
            final RuleSimplification simplifier =
                new RuleSimplification(rule, this.ng, this.aborter);
            final IGeneralizedRule simplyfiedRule = simplifier.simplify();
            TRSTerm condTerm = simplyfiedRule.getCondTerm();
            condTerm = condTerm == null ? ToolBox.buildTrue() : condTerm;
            if (!condTerm.equals(ToolBox.buildFalse())) {
                this.outputRules.add(simplyfiedRule);
            }
        }
    }
}
