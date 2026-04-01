package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;
import java.util.concurrent.atomic.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SAT.*;
import aprove.verification.dpframework.Orders.SAT.PLEncoders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Checks whether the TRS R is terminating because of bounded increase.
 *
 * higher level example:
 * <code>for i = 1 to 6 do something</code>
 * (increase of <i>i</i> up to upper bound <i>6</i> is detected)
 */
public class QDPBoundedIncreaseProcessor extends QDPProblemProcessor {

    private final static Logger logger = Logger.getLogger("aprove.verification.dpframework.TRSProblems.Processors."
        + "QDPBoundedIncreaseProcessor");

    private final Object constructorsLock = new Object(); // also for definedSymbols
    private final Object todoLock = new Object();
    private final Map<QDPProblem, AtomicInteger> counterMap = new LinkedHashMap<QDPProblem, AtomicInteger>(0);
    private volatile Map<QDPProblem, Set<Triple<Rule, Integer, Rule>>> todo =
        new LinkedHashMap<QDPProblem, Set<Triple<Rule, Integer, Rule>>>(0);
    private final Map<QDPProblem, Set<FunctionSymbol>> definedSymbols =
        new LinkedHashMap<QDPProblem, Set<FunctionSymbol>>(0);
    private volatile Map<QDPProblem, Set<FunctionSymbol>> constructors =
        new LinkedHashMap<QDPProblem, Set<FunctionSymbol>>(0);

    private final Engine engine;

    @ParamsViaArguments("Engine")
    public QDPBoundedIncreaseProcessor(final Engine engine) {
        assert (false) : "Please repair locking/synchronization before using this processor!";
        this.engine = engine;
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        assert (false) : "Please repair locking/synchronization before using this processor!";
        if (this.todo.get(qdp) == null) {
            // only synchronize if cache is not yet computed,
            // synchronize to omit multiple computation
            // store the number of threads currently working
            // on the given QDP (only delete information when
            // the last one finishes)
            synchronized (this.todoLock) {
                AtomicInteger counter = new AtomicInteger(0);
                if (this.counterMap.containsKey(qdp)) {
                    counter = this.counterMap.get(qdp);
                }
                counter.getAndIncrement();
                this.counterMap.put(qdp, counter);

                this.counterMap.put(qdp, counter);
                if (this.todo.get(qdp) == null) {

                    if (!qdp.getInnermost()) {
                        return false;
                    }

                    final Set<Triple<Rule, Integer, Rule>> todo = new LinkedHashSet<Triple<Rule, Integer, Rule>>(0);

                    final QDependencyGraph depGraph = qdp.getDependencyGraph();
                    if (depGraph.isSCC()) {
                        if (this.noSubCycles(depGraph)) { // having several subcycles implies checking all possible cycles, which is problematic
                            // check SCC and find (at least) one pair of rules with F(..) -> G(..cond(..)..) and G(..true..) -> ..
                            todo.addAll(this.checkScc(depGraph));
                            this.log(Level.FINER, "todo size: " + todo.size() + "\n");
                            this.todo.put(qdp, todo);
                        } else {
                            this.log(Level.FINER, "The SCC must not have a sub-cycle, aborting!\n");
                        }
                    } else {
                        this.log(Level.FINER, "The dependency graph is not a SCC, aborting.\n");
                    }
                }
            }
        }
        final boolean isApplicable = this.todo.containsKey(qdp) && this.todo.get(qdp).size() > 0;
        this.log(Level.FINER, "is applicable? " + isApplicable + "\n");
        return false;
        //return isApplicable;
    }

    private boolean noSubCycles(final QDependencyGraph scc) {
        if (Globals.useAssertions) {
            assert (scc.isSCC());
        }
        final Graph<Rule, ?> graph = scc.getGraph();
        for (final Node<Rule> node : graph.getNodes()) {
            if (graph.getOut(node).size() > 1) {
                return false;
            }
        }
        return true;
    }

    /**
     * This checks if the SCC contains the needed rules
     *      F(..)            -> G(.., cond(..), ..)
     *  and G(.., true, ...) -> ..
     *  If these rules can be found, a set describing them is returned (including the guessed "true" and its position in the terms)
     *
     * @param scc The dependency graph, that must be a SCC
     * @return A set containing rules of interest, if any
     */
    private Set<Triple<Rule, Integer, Rule>> checkScc(final QDependencyGraph scc) {
        /*
         * 1) F(..) -> G(.., cond(..), ..)
         * 2) G(.., true, ..) -> ..
         *
         * - at least one rule of type 1 has to be in this SCC
         * - exactly one rule of type 2 must be in the SCC
         * - the tuple symbol G must occur exactly once in the SCC
         */

        if (Globals.useAssertions) {
            assert (scc.isSCC());
        }

        final Set<Triple<Rule, Integer, Rule>> todo = new LinkedHashSet<Triple<Rule, Integer, Rule>>(0);
        for (final Node<Rule> node : scc.getNodesOnSCCs()) {
            final Rule rule = node.getObject();
            final TRSFunctionApplication left = rule.getLeft();
            final Set<Integer> results = this.findTrue(left); // find all valid constructors that can be the "true" we need
            if (results.size() > 0) { // found a constructor (maybe "true"?) in this lhs
                final FunctionSymbol symbolG = left.getRootSymbol();
                for (final Integer argumentNum : results) {
                    final Set<Rule> resultRules = this.findTest(argumentNum, symbolG, scc);
                    if (resultRules.size() > 0) {
                        // found a rule that has G(.., cond(..), ..)
                        for (final Rule condRule : resultRules) {
                            // check for "bounded increase" with this constructor ("true"?) and the "cond" rule
                            final Triple<Rule, Integer, Rule> todoTriple =
                                new Triple<Rule, Integer, Rule>(rule, argumentNum, condRule);
                            todo.add(todoTriple);
                        }

                    }
                }
            }
        }
        return todo;
    }

    private Set<Integer> findTrue(final TRSFunctionApplication left) {
        // scan the given left side of the term and find all valid "true"s (as in G(.., true, ..))
        // additionally check if the left side carries at least one argument (the ascending one)

        final Set<Integer> results = new LinkedHashSet<Integer>(0);
        final int numArguments = left.getArguments().size();
        if (numArguments >= 2) {
            // "true" and ascending
            for (int i = 0; i < numArguments; i++) {
                final TRSTerm argument = left.getArgument(i);
                if (argument instanceof TRSFunctionApplication) {
                    final TRSFunctionApplication application = (TRSFunctionApplication) argument;
                    if (application.getArguments().size() == 0) {
                        this.log(Level.FINER, "The argument " + (i + 1) + " (" + application.getRootSymbol().toString()
                            + ") of lhs " + left.toString()
                            + " is a constructor, maybe the 'true' we are looking for?\n");
                        results.add(Integer.valueOf(i));
                    }
                }
            }
        }
        return results;
    }

    private Set<Rule> findTest(final Integer argumentNum, final FunctionSymbol symbolG, final QDependencyGraph scc) {
        // check all rules except rule "rule", find out if argument number argumentNum is of form "cond(..)"
        // additionally check if cond(..) has at least two arguments (ascending, descending)

        final Set<Rule> results = new LinkedHashSet<Rule>(0);
        for (final Node<Rule> node : scc.getNodesOnSCCs()) {
            final Rule rule = node.getObject();
            TRSFunctionApplication rightF = null;
            if (rule.getRight() instanceof TRSFunctionApplication) {
                rightF = (TRSFunctionApplication) rule.getRight();
            }
            final FunctionSymbol leftSymbol = rule.getLeft().getRootSymbol();
            if ((!leftSymbol.equals(symbolG) || (rightF != null && rightF.getRootSymbol().equals(symbolG))) // no additional rule with symbol G
                && !rule.getRight().isVariable()) { // the rhs is no variable, so there might be a condition inside
                if (rightF.getRootSymbol().equals(symbolG) // rule of type F(..) -> G(..)
                    && rightF.getArguments().size() >= argumentNum) {
                    final TRSTerm argument = rightF.getArgument(argumentNum);
                    if (!argument.isVariable()) {
                        final TRSFunctionApplication functionApplication = (TRSFunctionApplication) argument;
                        if (functionApplication.getArguments().size() >= 2) {
                            // rule of type F(..) -> G(..,something(a,b,..),..)
                            this.log(Level.INFO, "the rule " + rule.toString() + " looks promising!\n");
                            results.add(rule);
                        }
                    }
                }
            }
        }
        return results;
    }

    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter) throws AbortionException {
        try {
            this.calculateConstructors(qdp); // prepare two static sets containing constructors and defined symbols of the QDP
            aborter.checkAbortion();

            final FormulaFactory<None> factory = new FullSharingFactory<None>();
            final SATPatterns<None> satPatterns = new SATPatterns<None>(factory);
            final SATChecker satChecker = this.engine.getSATChecker();

            for (final Triple<Rule, Integer, Rule> problem : this.todo.get(qdp)) {
                // it suffices to prove termination for one element of todo
                final Pair<Result, Boolean> result =
                    this.processSmallerProblem(problem, aborter, qdp, factory, satPatterns, satChecker);
                if (result.y) {
                    return result.x;
                }
            }
            this.cleanup(qdp); // we are done with this QDP
            return ResultFactory.unsuccessful();
        } catch (final AbortionException e) {
            this.cleanup(qdp);
            throw e;
        }
    }

    private Pair<Result, Boolean> processSmallerProblem(final Triple<Rule, Integer, Rule> problem,
        final Abortion aborter,
        final QDPProblem qdp,
        final FormulaFactory<None> factory,
        final SATPatterns<None> satPatterns,
        final SATChecker satChecker) throws AbortionException {
        aborter.checkAbortion();

        final Map<Variable<None>, String> variableToString = new LinkedHashMap<Variable<None>, String>(0); // collect information for each used variable to have a readable output

        /* y is the position of the cond argument in the rhs of term z and in the lhs of x
         * example:
         * x: if(true,a,b) -> f(s(a),b)
         *         ^
         * y: 0    |         |
         *                   v
         * z: f(a,b) -> if(le(a,b),a,b)
         */

        final TRSFunctionApplication right = (TRSFunctionApplication) problem.z.getRight();
        final TRSTerm condition = right.getArgument(problem.y); // cond() in: F(..) -> G(..,cond(..),..)
        final FunctionSymbol conditionSymbol = ((TRSFunctionApplication) condition).getRootSymbol(); // cond

        final TRSTerm trueTerm = problem.x.getLeft().getArgument(problem.y); // "true"

        final List<Rule> condToTrueRules = this.findToTrueRules(qdp, condition, trueTerm);
        if (condToTrueRules.size() == 0) {
            // no Rule cond(..) -> true was found
            this.log(Level.FINE, "failing, because no rule cond()->true was found\n");
            return new Pair<Result, Boolean>(null, false);
        }

        // test if rules of form OTHER than cond()->constructor and cond()->cond() exist
        if (this.findBadRules(qdp, conditionSymbol)) {
            // a rule cond()-> .. was found where the rhs is not a constructor and not cond(..)
            this.log(Level.FINE,
                "failing, because a rule cond()->'something' was found where 'something' is neither cond() nor a constructor term\n");
            return new Pair<Result, Boolean>(null, false);
        }

        // argument filtering: see paper "SAT Solving for Argument Filterings"
        final Map<FunctionSymbol, List<Variable<None>>> filterArg =
            new LinkedHashMap<FunctionSymbol, List<Variable<None>>>(0); // collect variables defining the argument-part of the argument filtering
        final Map<FunctionSymbol, Variable<None>> filterList = new LinkedHashMap<FunctionSymbol, Variable<None>>(0); // collect variables defining the (non)flattening part of the argument filtering

        // the map includes all new constraints (that have to be fulfilled later) and for each constraint the corresponding variable that defines when the constraint has to be fulfilled
        Map<Constraint<TRSTerm>, Variable<None>> constraintMap = new LinkedHashMap<Constraint<TRSTerm>, Variable<None>>();

        // these maps contain variables defining which argument is ascending/descending (or if the symbol has a descending argument)
        final Map<FunctionSymbol, List<Variable<None>>> variablesAscending =
            new LinkedHashMap<FunctionSymbol, List<Variable<None>>>();
        final Map<FunctionSymbol, List<Variable<None>>> variablesDescending =
            new LinkedHashMap<FunctionSymbol, List<Variable<None>>>();
        final Map<FunctionSymbol, Variable<None>> variableDescendingDummy =
            new LinkedHashMap<FunctionSymbol, Variable<None>>();

        // only constraints collected in part 3a may define a bottom symbol (in the PO)
        final Set<Constraint<TRSTerm>> constraints3a = new LinkedHashSet<Constraint<TRSTerm>>();

        // the important part: build the formula that is solvable iff termination can be proven
        Formula<None> formula =
            this.buildFormula(qdp, factory, aborter, condToTrueRules, variableToString, satPatterns, variablesAscending,
                variablesDescending, variableDescendingDummy, filterList, filterArg, constraintMap, constraints3a,
                problem);

        // collect all terms and symbols used in the constraints
        final Set<TRSTerm> terms = new LinkedHashSet<TRSTerm>(); // FIXME needed?
        final Set<FunctionSymbol> functionSymbols = new LinkedHashSet<FunctionSymbol>();

        for (final Constraint<TRSTerm> constraint : constraintMap.keySet()) {
            this.buildSymbols(constraint.x, terms, functionSymbols);
            this.buildSymbols(constraint.y, terms, functionSymbols);
        }

        // build up the variables for argument filtering, at least for the basic function symbols (others may need variables too, these are added on the fly)
        this.prepareArgumentFiltering(functionSymbols, filterList, filterArg, factory, variableToString, satPatterns,
            formula);

        // directly encode EQ, handle GE as (EQ or GR)
        final Pair<Map<Constraint<TRSTerm>, Variable<None>>, Formula<None>> constraintPair =
            this.transformConstraints(constraintMap, factory, formula, variableToString, constraints3a);
        constraintMap = constraintPair.x;
        formula = constraintPair.y;

        final Map<Variable<None>, Fact> poConstraints = new LinkedHashMap<Variable<None>, Fact>();
        final List<Variable<None>> bottomSymbols = new LinkedList<Variable<None>>();

        // generate constraints according to LPO definition, prepare formula for PLEncoder
        final Pair<Formula<None>, Formula<None>> formulaPair =
            this.encodeConstraints(constraintMap, aborter, constraints3a, factory, formula, variableToString, poConstraints,
                bottomSymbols, filterArg, filterList);
        final Formula<None> constraintFormula = formulaPair.x;
        formula = formulaPair.y;

        // take care that the filtering is done correctly
        for (final Map.Entry<FunctionSymbol, Variable<None>> entry : filterList.entrySet()) {
            final FunctionSymbol symbol = entry.getKey();
            final Variable<None> varList = entry.getValue();
            final List<Variable<None>> varsArgs = filterArg.get(symbol);

            // if the filtering is collapsing, only collapse to exactly one argument
            final Formula<None> exactlyOne = satPatterns.encodeExactlyOne(filterArg.get(symbol));
            Formula<None> newFormula = factory.buildOr(varList, exactlyOne);

            // do not filter away arguments that are ascending/descending
            if (variablesAscending.containsKey(symbol)) {
                for (int i = 0; i < varsArgs.size(); i++) {
                    final Formula<None> implicationAsc =
                        factory.buildImplication(variablesAscending.get(symbol).get(i), varsArgs.get(i));
                    final Formula<None> implicationDesc =
                        factory.buildImplication(variablesDescending.get(symbol).get(i), varsArgs.get(i));
                    newFormula = factory.buildAnd(newFormula, implicationAsc, implicationDesc);
                }
            }

            formula = factory.buildAnd(formula, newFormula);
        }

        if (bottomSymbols.size() > 1) {
            // only one bottom symbol is allowed
            final Formula<None> oneBottom = satPatterns.encodeExactlyOne(bottomSymbols);
            formula = factory.buildAnd(formula, oneBottom);
        }

        // encode the collected constraints on symbols (f > g) using the PLEncoder
        final PLEncoder encoder = new SimpleBinaryPLEncoder(factory, true); // TODO make this configurable to enable selection of other PLEncoders
        final POFormula poFormula = new POFormula(constraintFormula, poConstraints, factory, true);
        final Formula<None> encodedConstraintFormula = encoder.toPropositionalFormula(poFormula, aborter);
        formula = factory.buildAnd(formula, encodedConstraintFormula);

        /* TODO
         * I don't know how to handle a fail on this.
         * For now it will be handled as unsatisfiable.
         * Please check this.
         *
         * -- thetux
         */
        int[] result;
        try {
            result = satChecker.solve(formula, aborter);
        } catch (final SolverException e) {
            result = null;
        }
        if (result != null) {
            this.log(Level.INFO, "solved! Solution:\n");
            this.log(Level.INFO, "Partial Order for Function Symbols:\n" + this.getPoSet(poConstraints, result) + "\n");
            final TRSFunctionApplication conditionF = (TRSFunctionApplication) condition;
            final String proofText = this.getSolution(result, conditionF.getRootSymbol(), variableToString);
            this.log(Level.INFO, proofText + "\n");

            this.cleanup(qdp); // we are done with this QDP
            final Result resultProof =
                ResultFactory.proved(this.getQdpWithoutP(qdp), YNMImplication.EQUIVALENT, new BoundedIncreaseProof(qdp,
                    proofText));
            return new Pair<Result, Boolean>(resultProof, true);
        } else {
            return new Pair<Result, Boolean>(null, false);
        }
    }

    private Pair<Formula<None>, Formula<None>> encodeConstraints(final Map<Constraint<TRSTerm>, Variable<None>> constraintMap,
        final Abortion aborter,
        final Set<Constraint<TRSTerm>> constraints3a,
        final FormulaFactory<None> factory,
        Formula<None> formula,
        final Map<Variable<None>, String> variableToString,
        final Map<Variable<None>, Fact> poConstraints,
        final List<Variable<None>> bottomSymbols,
        final Map<FunctionSymbol, List<Variable<None>>> filterArg,
        final Map<FunctionSymbol, Variable<None>> filterList) throws AbortionException {
        Formula<None> constraintFormula = factory.buildConstant(true);
        for (final Map.Entry<Constraint<TRSTerm>, Variable<None>> entry : constraintMap.entrySet()) {
            final Constraint<TRSTerm> constraint = entry.getKey();
            final Variable<None> varConstraint = entry.getValue();
            aborter.checkAbortion();

            if (Globals.useAssertions) {
                assert (constraint.z.equals(OrderRelation.GR));
            }
            if (!(constraint.x instanceof TRSFunctionApplication)) {

                // in the example from the paper the constraint "y > 0" must be fulfilled, so try to handle this by defining "0" as a bottom symbol
                if (constraint.y instanceof TRSFunctionApplication && constraints3a.contains(constraint)) {
                    final FunctionSymbol symbol = ((TRSFunctionApplication) constraint.y).getRootSymbol();
                    final Variable<None> var = factory.buildVariable();
                    final Fact fact = new FactBot(symbol);
                    variableToString.put(var, "The fact '" + fact + "' is fulfilled");
                    poConstraints.put(var, fact);
                    constraintFormula =
                        factory.buildAnd(constraintFormula, factory.buildImplication(varConstraint, var));
                    bottomSymbols.add(var);
                } else {
                    // this constraint cannot be fulfilled
                    final Formula<None> newFormula = factory.buildNot(varConstraint);
                    formula = factory.buildAnd(formula, newFormula);
                }
            } else {
                Formula<None> newFormula =
                    this.buildGr(constraint.x, constraint.y, factory, filterArg, filterList, poConstraints,
                        variableToString);
                newFormula = factory.buildImplication(varConstraint, newFormula);
                constraintFormula = factory.buildAnd(constraintFormula, newFormula);
            }
        }
        return new Pair<Formula<None>, Formula<None>>(constraintFormula, formula);
    }

    private Pair<Map<Constraint<TRSTerm>, Variable<None>>, Formula<None>> transformConstraints(final Map<Constraint<TRSTerm>, Variable<None>> constraintMap,
        final FormulaFactory<None> factory,
        Formula<None> formula,
        final Map<Variable<None>, String> variableToString,
        final Set<Constraint<TRSTerm>> constraints3a) {
        final Map<Constraint<TRSTerm>, Variable<None>> newConstraintMap =
            new LinkedHashMap<Constraint<TRSTerm>, Variable<None>>();
        for (final Map.Entry<Constraint<TRSTerm>, Variable<None>> entry : constraintMap.entrySet()) {
            final Constraint<TRSTerm> constraint = entry.getKey();
            final Variable<None> var = entry.getValue();
            if (constraint.z.equals(OrderRelation.EQ)) {
                if (!constraint.x.equals(constraint.y)) {
                    Formula<None> newFormula;
                    newFormula = factory.buildNot(var);
                    formula = factory.buildAnd(formula, newFormula);
                }
            } else if (constraint.z.equals(OrderRelation.GE)) {
                if (!constraint.x.equals(constraint.y)) {
                    final Variable<None> varConstraint = var;
                    final Constraint<TRSTerm> newConstraint = Constraint.create(constraint.x, constraint.y, OrderRelation.GR);
                    if (constraints3a.contains(constraint)) {
                        constraints3a.add(newConstraint);
                    }
                    final Variable<None> varNewConstraint =
                        this.getFromConstraintMap(newConstraintMap, newConstraint, factory, variableToString);
                    // ensure that the GR constraint is fulfilled whenever the GE constraint has to be fulfilled (here GE=GR, because EQ does not hold)
                    formula = factory.buildAnd(formula, factory.buildIff(varConstraint, varNewConstraint));
                }
            } else if (constraint.z.equals(OrderRelation.GR)) {
                newConstraintMap.put(constraint, var); // do not use getFromConstraintMap, because a new variable would be created
            }
        }
        return new Pair<Map<Constraint<TRSTerm>, Variable<None>>, Formula<None>>(newConstraintMap, formula);
    }

    private void prepareArgumentFiltering(final Set<FunctionSymbol> functionSymbols,
        final Map<FunctionSymbol, Variable<None>> filterList,
        final Map<FunctionSymbol, List<Variable<None>>> filterArg,
        final FormulaFactory<None> factory,
        final Map<Variable<None>, String> variableToString,
        final SATPatterns<None> satPatterns,
        final Formula<None> formula) {
        for (final FunctionSymbol symbol : functionSymbols) {
            if (!filterArg.containsKey(symbol)) {
                // not yet done
                final int arity = symbol.getArity();
                final List<Variable<None>> argf = factory.buildVariables(arity);
                for (int i = 0; i < arity; i++) {
                    variableToString.put(argf.get(i), "The argument #" + (i + 1) + " of symbol '" + symbol
                        + "' is not filtered.");
                }
                filterArg.put(symbol, argf);

                final Variable<None> listf = factory.buildVariable();
                variableToString.put(listf, "The symbol '" + symbol + "' is filtered to a list.");
                filterList.put(symbol, listf);
            }
        }
    }

    private Formula<None> buildFormula(final QDPProblem qdp,
        final FormulaFactory<None> factory,
        final Abortion aborter,
        final List<Rule> condToTrueRules,
        final Map<Variable<None>, String> variableToString,
        final SATPatterns<None> satPatterns,
        final Map<FunctionSymbol, List<Variable<None>>> variablesAscending,
        final Map<FunctionSymbol, List<Variable<None>>> variablesDescending,
        final Map<FunctionSymbol, Variable<None>> variableDescendingDummy,
        final Map<FunctionSymbol, Variable<None>> filterList,
        final Map<FunctionSymbol, List<Variable<None>>> filterArg,
        final Map<Constraint<TRSTerm>, Variable<None>> constraintMap,
        final Set<Constraint<TRSTerm>> constraints3a,
        final Triple<Rule, Integer, Rule> problem) throws AbortionException {
        // now generate a huge formula, build up from the 5 parts of the paper
        aborter.checkAbortion();
        final Formula<None> formula1 =
            this.buildFormulaPre(qdp, factory, aborter, condToTrueRules, variableToString, satPatterns, variablesAscending,
                variablesDescending, variableDescendingDummy); // guess ascending and descending arguments

        aborter.checkAbortion();
        final Formula<None> formula2 =
            this.buildFormula1and2(qdp, factory, aborter, variableToString, filterList, filterArg, variablesAscending,
                variablesDescending, variableDescendingDummy, constraintMap);

        aborter.checkAbortion();

        final Formula<None> formula3a =
            this.buildFormula3a(factory, aborter, condToTrueRules, variableToString, variablesAscending,
                variablesDescending, constraints3a, constraintMap);

        aborter.checkAbortion();
        final Formula<None> formula3b =
            this.buildFormula3b(qdp, factory, aborter, condToTrueRules, variableToString, variablesAscending,
                variablesDescending);

        aborter.checkAbortion();
        final Formula<None> formula4 =
            this.buildFormula4(qdp, factory, aborter, condToTrueRules, problem.z, problem.y, filterArg, variablesAscending);

        aborter.checkAbortion();
        final Formula<None> formula5 =
            this.buildFormula5(qdp, factory, aborter, condToTrueRules, problem.z, problem.y, filterArg, variablesAscending,
                variablesDescending, variableDescendingDummy);

        Formula<None> formula = factory.buildAnd(formula1, formula2, formula3a);
        formula = factory.buildAnd(formula, formula3b, formula4);
        formula = factory.buildAnd(formula, formula5);
        return formula;
    }

    private void cleanup(final QDPProblem qdp) {
        if (this.counterMap.containsKey(qdp)) {
            final AtomicInteger counter = this.counterMap.get(qdp);
            if (counter.decrementAndGet() == 0) {
                // no other thread is working with this QDP, so delete the cached information
                if (this.todo.containsKey(qdp)) {
                    this.todo.remove(qdp);
                }
                if (this.constructors.containsKey(qdp)) {
                    this.constructors.remove(qdp);
                }
                if (this.definedSymbols.containsKey(qdp)) {
                    this.definedSymbols.remove(qdp);
                }
                this.counterMap.remove(qdp);
            }
        }
    }

    private void buildSymbols(final TRSTerm term, final Set<TRSTerm> terms, final Set<FunctionSymbol> functionSymbols) {
        terms.add(term);
        if (term instanceof TRSFunctionApplication) {
            final TRSFunctionApplication func = (TRSFunctionApplication) term;
            final FunctionSymbol symbol = func.getRootSymbol();
            functionSymbols.add(symbol);
            for (final TRSTerm subterm : func.getArguments()) {
                this.buildSymbols(subterm, terms, functionSymbols);
            }
        }
    }

    /*
     * the sat checker returns some numbers as solution, so this function tries to give some sense to the result
     */
    private String getSolution(final int[] resultInts,
        final FunctionSymbol condition,
        final Map<Variable<None>, String> variableToString) {
        final Map<Integer, Variable<None>> mapInt = new LinkedHashMap<Integer, Variable<None>>(variableToString.size());
        final StringBuilder sb = new StringBuilder();

        for (final Variable<None> var : variableToString.keySet()) {
            mapInt.put(var.getId(), var);
        }
        for (final Integer subject : resultInts) {
            if (mapInt.containsKey(subject)) {
                sb.append(variableToString.get(mapInt.get(subject)));
                sb.append("\n");
            }
        }
        sb.append("condition: '");
        sb.append(condition);
        sb.append("'\n");
        return sb.toString();
    }

    /**
     * generate a formula that "guesses" ascending and descending positions for every needed function symbol
     */
    private Formula<None> buildFormulaPre(final QDPProblem qdp,
        final FormulaFactory<None> factory,
        final Abortion aborter,
        final List<Rule> condToTrueRules,
        final Map<Variable<None>, String> variableToString,
        final SATPatterns<None> satPatterns,
        final Map<FunctionSymbol, List<Variable<None>>> variablesAscending,
        final Map<FunctionSymbol, List<Variable<None>>> variablesDescending,
        final Map<FunctionSymbol, Variable<None>> variableDescendingDummy) {

        Formula<None> formula = factory.buildConstant(true);

        final FunctionSymbol condition = condToTrueRules.get(0).getLeft().getRootSymbol();

        // build two variables for every argument of cond(..)
        final int condArity = condition.getArity();
        final List<Variable<None>> ascendingCondition = factory.buildVariables(condArity);
        final List<Variable<None>> descendingCondition = factory.buildVariables(condArity);

        final List<Variable<None>> ascExactlyOne = new LinkedList<Variable<None>>();
        final List<Variable<None>> descExactlyOne = new LinkedList<Variable<None>>();

        for (int i = 0; i < condArity; i++) {
            // remember meaning of the variables for later output
            variableToString.put(ascendingCondition.get(i), "Argument #" + (i + 1) + " of condition ('" + condition
                + "') is ascending.");
            variableToString.put(descendingCondition.get(i), "Argument #" + (i + 1) + " of condition ('" + condition
                + "') is descending.");

            // one argument cannot be ascending and descending
            formula =
                factory.buildAnd(formula,
                    factory.buildNot(factory.buildAnd(ascendingCondition.get(i), descendingCondition.get(i))));
            ascExactlyOne.add(ascendingCondition.get(i));
            descExactlyOne.add(descendingCondition.get(i));
        }

        // exactly one argument has to be ascending / descending
        final Formula<None> xorFormulaAsc = satPatterns.encodeExactlyOne(ascExactlyOne);
        final Formula<None> xorFormulaDesc = satPatterns.encodeExactlyOne(descExactlyOne);
        formula = factory.buildAnd(formula, xorFormulaAsc, xorFormulaDesc);

        variablesAscending.put(condition, ascendingCondition);
        variablesDescending.put(condition, descendingCondition);

        // collect all occurring function symbols to guess ascending/descending positions
        final Set<FunctionSymbol> functionSymbols = this.collectPSymbols(qdp.getP());

        // only guess asc/desc for the function symbols that matter
        for (final FunctionSymbol functionSymbol : functionSymbols) {
            if (!variablesAscending.containsKey(functionSymbol) && functionSymbol.getArity() >= 1) { // constants have no (ascending) argument
                /*
                 * the generated formula ensures:
                 * 1) desc != asc (for each defined symbol)
                 * 2) every function symbol has exactly one ascending position
                 * 3) every function symbol has exactly one descending position (where this might be a dummy, meaning the function symbol has no descending argument)
                 */
                Formula<None> formulaNew = factory.buildConstant(true);

                // generate variables for every argument of that symbol
                // each such variabel is true iff the corresponding argument is the ascending one
                final List<Variable<None>> positionsAsc = factory.buildVariables(functionSymbol.getArity());
                variablesAscending.put(functionSymbol, positionsAsc);
                for (int i = 0; i < positionsAsc.size(); i++) {
                    variableToString.put(positionsAsc.get(i), "Argument #" + (i + 1) + " of function symbol '"
                        + functionSymbol + "' is ascending.");
                }

                // generate variables for every argument of that symbol
                // each such variable is true iff the corresponding argument is the descending one
                final List<Variable<None>> positionsDesc = factory.buildVariables(functionSymbol.getArity());
                variablesDescending.put(functionSymbol, positionsDesc);
                for (int i = 0; i < positionsDesc.size(); i++) {
                    variableToString.put(positionsDesc.get(i), "Argument #" + (i + 1) + " of function symbol '"
                        + functionSymbol + "' is descending.");
                }

                // there might be no descending argument in this term, so set a dummy variable
                final Variable<None> dummyVar = factory.buildVariable();
                variableToString.put(dummyVar, "The function symbol '" + functionSymbol
                    + "' has no descending argument.");
                variableDescendingDummy.put(functionSymbol, dummyVar);

                // exactly one argument has to be ascending
                final Formula<None> asc = satPatterns.encodeExactlyOne(positionsAsc);
                // exactly one argument has to be descending or no argument is descending
                Formula<None> descOne = satPatterns.encodeExactlyOne(positionsDesc);
                descOne = factory.buildAnd(factory.buildNot(dummyVar), descOne);

                final List<Formula<None>> positionsDescFormula = new LinkedList<Formula<None>>(positionsDesc);
                Formula<None> descNone = factory.buildNot(factory.buildOr(positionsDescFormula));
                descNone = factory.buildAnd(descNone, dummyVar);

                final Formula<None> desc = factory.buildOr(descOne, descNone);

                // now ensure that no argument is ascending AND descending
                for (int i = 0; i < positionsAsc.size(); i++) {
                    final Formula<None> notSame =
                        factory.buildNot(factory.buildAnd(positionsAsc.get(i), positionsDesc.get(i)));
                    formulaNew = factory.buildAnd(formulaNew, notSame);
                }

                // this formula now ensures that the current function symbol has a correct ascending and a correct descending argument
                formulaNew = factory.buildAnd(formulaNew, asc, desc);

                formula = factory.buildAnd(formula, formulaNew);
            }
        }

        return formula;
    }

    private Set<FunctionSymbol> collectPSymbols(final Set<Rule> rules) {
        final Set<FunctionSymbol> functionSymbols = new LinkedHashSet<FunctionSymbol>();
        for (final Rule rule : rules) {
            functionSymbols.add(rule.getLeft().getRootSymbol());
            functionSymbols.add(((TRSFunctionApplication) rule.getRight()).getRootSymbol());
        }
        return functionSymbols;
    }

    private Formula<None> buildFormula1and2(final QDPProblem qdp,
        final FormulaFactory<None> factory,
        final Abortion aborter,
        final Map<Variable<None>, String> variableToString,
        final Map<FunctionSymbol, Variable<None>> filterList,
        final Map<FunctionSymbol, List<Variable<None>>> filterArg,
        final Map<FunctionSymbol, List<Variable<None>>> variablesAscending,
        final Map<FunctionSymbol, List<Variable<None>>> variablesDescending,
        final Map<FunctionSymbol, Variable<None>> variableDescendingDummy,
        final Map<Constraint<TRSTerm>, Variable<None>> constraintMap) {

        Formula<None> formula = factory.buildConstant(true);

        // compute the usable rules U(P, A, pi) and U(P, D, pi), so take into account which arguments are ascending/descending
        final QUsableRules qUsableRules = new QUsableRules(qdp.getRwithQ());
        final Map<Rule, QActiveCondition> active = qUsableRules.getActiveConditions(qdp.getP(), false);

        final Set<Pair<Formula<None>, Rule>> usableRulesAsc = new LinkedHashSet<Pair<Formula<None>, Rule>>();
        final Set<Pair<Formula<None>, Rule>> usableRulesDesc = new LinkedHashSet<Pair<Formula<None>, Rule>>();

        this.getUsableRules(qdp, active, variablesAscending, variablesDescending, factory, filterList, filterArg,
            variableToString, usableRulesAsc, usableRulesDesc);

        // a rule contained in one of these sets is usable, if the corresponding formula is fulfilled.
        // Example: Some rule X is only usable if some argument Y is ascending. The formula then would be "Y is ascending".

        // for every rule in U(P, A, pi) ensure that "lhs <= rhs"
        for (final Pair<Formula<None>, Rule> pair : usableRulesAsc) {
            final Formula<None> formulaU = pair.x;
            final Rule ruleU = pair.y;
            final Constraint<TRSTerm> constraint = Constraint.create(ruleU.getRight(), ruleU.getLeft(), OrderRelation.GE);
            final Variable<None> constraintVar =
                this.getFromConstraintMap(constraintMap, constraint, factory, variableToString); // create the variable and store output information for this constraint

            // the current rule is only a usable rule, if the formula is fulfilled.
            // Therefore: If the rule is fulfilled, ensure that the constraint is fulfilled
            final Formula<None> newFormula = factory.buildImplication(formulaU, constraintVar);
            formula = factory.buildAnd(formula, newFormula);
        }

        // same thing for descending rules
        for (final Pair<Formula<None>, Rule> pair : usableRulesDesc) {
            final Formula<None> formulaU = pair.x;
            final Rule ruleU = pair.y;
            final Constraint<TRSTerm> constraint = Constraint.create(ruleU.getLeft(), ruleU.getRight(), OrderRelation.GE);
            final Variable<None> constraintVar =
                this.getFromConstraintMap(constraintMap, constraint, factory, variableToString);
            final Formula<None> newFormula = factory.buildImplication(formulaU, constraintVar);
            formula = factory.buildAnd(formula, newFormula);
        }

        // formula that ensures strict increase somewhere in the cycle
        Formula<None> strictIncrease = factory.buildConstant(false);

        // for every DP where both sides have at least one argument (ascending and perhaps descending): build constraints according to parts 1 and 2 of the paper
        for (final Rule rule : qdp.getP()) {
            if (rule.getLeft().getRootSymbol().getArity() >= 1 && !rule.getRight().isVariable()
                && ((TRSFunctionApplication) rule.getRight()).getRootSymbol().getArity() >= 1) {
                // get the variables describing that the left/right side has no descending argument
                final Variable<None> dummyLeft = variableDescendingDummy.get(rule.getLeft().getRootSymbol());
                final Variable<None> dummyRight =
                    variableDescendingDummy.get(((TRSFunctionApplication) rule.getRight()).getRootSymbol());

                // if one side has no descending argument, the other side must also have no descending argument
                final Formula<None> noDescendingArg = factory.buildIff(dummyLeft, dummyRight);

                final TRSFunctionApplication rightF = (TRSFunctionApplication) rule.getRight();

                // now go through every combination of left and right argument to build contraints, depending on the guesses for ascending/descending arguments
                for (int i = 0; i < rule.getLeft().getRootSymbol().getArity(); i++) {
                    final List<Variable<None>> listVarsAscLeft = variablesAscending.get(rule.getLeft().getRootSymbol());
                    // get the variable defining if the current argument of the left term at position i is ascending
                    final Variable<None> varAscLeft = listVarsAscLeft.get(i);

                    // get the variable defining if the current argument of the left term at position i is descending
                    final Variable<None> varDescLeft = variablesDescending.get(rule.getLeft().getRootSymbol()).get(i);

                    for (int j = 0; j < rightF.getRootSymbol().getArity(); j++) {
                        // get the variable defining if the current argument of the right term at position i is ascending
                        final Variable<None> varAscRight = variablesAscending.get(rightF.getRootSymbol()).get(j);
                        // get the variable defining if the current argument of the right term at position i is descending
                        final Variable<None> varDescRight = variablesDescending.get(rightF.getRootSymbol()).get(j);

                        // ascending argument in the left term must be <= the ascending argument in the right term
                        final Constraint<TRSTerm> constraintAsc =
                            Constraint.create(rightF.getArgument(j), rule.getLeft().getArgument(i), OrderRelation.GE);

                        // descending argument in the left term must be >= the descending argument in the right term
                        final Constraint<TRSTerm> constraintDesc =
                            Constraint.create(rule.getLeft().getArgument(i), rightF.getArgument(j), OrderRelation.GE);

                        // if the terms at positions i/j represent the ascending arguments then the constraint must hold
                        Formula<None> newConstraintAsc;
                        final Variable<None> constraintAscVariable =
                            this.getFromConstraintMap(constraintMap, constraintAsc, factory, variableToString);
                        newConstraintAsc =
                            factory.buildImplication(factory.buildAnd(varAscLeft, varAscRight), constraintAscVariable);

                        // descending
                        Formula<None> newConstraintDesc;
                        final Variable<None> constraintDescVariable =
                            this.getFromConstraintMap(constraintMap, constraintDesc, factory, variableToString);
                        newConstraintDesc =
                            factory.buildImplication(factory.buildAnd(varDescLeft, varDescRight),
                                constraintDescVariable);

                        /*
                         * strict increase
                         * after completion this strictIncrease formula reads:
                         *      false
                         *   OR foo1 and bar1 are the ascending arguments and foo1 < bar1 holds
                         *   OR foo2 and bar2 are the ascending arguments and foo2 < bar2 holds
                         *   OR ..
                         *   meaning: at least one guess of asc/desc results in strict foo < bar
                         */
                        final Constraint<TRSTerm> constraintStrictAsc =
                            Constraint.create(rightF.getArgument(j), rule.getLeft().getArgument(i), OrderRelation.GR);
                        final Variable<None> constraintStrictAscVariable =
                            this.getFromConstraintMap(constraintMap, constraintStrictAsc, factory, variableToString);
                        final Formula<None> newFormulaStrict =
                            factory.buildAnd(varAscLeft, varAscRight, constraintStrictAscVariable);
                        strictIncrease = factory.buildOr(strictIncrease, newFormulaStrict);

                        // now constraintMap includes constraint->variable
                        // this information is later used to actually build the constraints
                        // which have to be fulfilled whenever the corresponding variable is set

                        final Formula<None> newFormula =
                            factory.buildAnd(noDescendingArg, newConstraintAsc, newConstraintDesc);
                        formula = factory.buildAnd(formula, newFormula);
                    }
                }
            }
        }
        formula = factory.buildAnd(formula, strictIncrease);
        return formula;
    }

    private Formula<None> buildFormula3a(final FormulaFactory<None> factory,
        final Abortion aborter,
        final List<Rule> condToTrueRules,
        final Map<Variable<None>, String> variableToString,
        final Map<FunctionSymbol, List<Variable<None>>> variablesAscending,
        final Map<FunctionSymbol, List<Variable<None>>> variablesDescending,
        final Set<Constraint<TRSTerm>> constraints3a,
        final Map<Constraint<TRSTerm>, Variable<None>> constraintMap) {
        // build constraints according to 3a (cond -> true)

        final FunctionSymbol condition = condToTrueRules.get(0).getLeft().getRootSymbol();

        Formula<None> condToTrueFormula = factory.buildConstant(true);
        final List<Variable<None>> ascendingInCond = variablesAscending.get(condition);
        final List<Variable<None>> descendingInCond = variablesDescending.get(condition);

        for (int i = 0; i < ascendingInCond.size(); i++) {
            for (int j = 0; j < descendingInCond.size(); j++) {
                if (i != j) { // there is no argument that is ascending and descending
                    for (final Rule condToTrue : condToTrueRules) {
                        final TRSTerm asc = condToTrue.getLeft().getArgument(i);
                        final TRSTerm desc = condToTrue.getLeft().getArgument(j);
                        final Variable<None> ascVar = ascendingInCond.get(i);
                        final Variable<None> descVar = descendingInCond.get(j);

                        final Constraint<TRSTerm> constraint = Constraint.create(desc, asc, OrderRelation.GE); // asc <= desc, e.g. y <= 0 in the paper
                        final Variable<None> constraintVar =
                            this.getFromConstraintMap(constraintMap, constraint, factory, variableToString);
                        constraints3a.add(constraint);

                        final Formula<None> newFormula =
                            factory.buildImplication(factory.buildAnd(ascVar, descVar), constraintVar);
                        condToTrueFormula = factory.buildAnd(condToTrueFormula, newFormula);
                    }
                }
            }
        }
        return condToTrueFormula;
    }

    private Formula<None> buildFormula3b(final QDPProblem qdp,
        final FormulaFactory<None> factory,
        final Abortion aborter,
        final List<Rule> condToTrueRules,
        final Map<Variable<None>, String> variableToString,
        final Map<FunctionSymbol, List<Variable<None>>> variablesAscending,
        final Map<FunctionSymbol, List<Variable<None>>> variablesDescending) {
        final FunctionSymbol condition = condToTrueRules.get(0).getLeft().getRootSymbol();
        final List<Variable<None>> ascendingInCond = variablesAscending.get(condition);
        final List<Variable<None>> descendingInCond = variablesDescending.get(condition);

        Formula<None> condToCondFormula = factory.buildConstant(true);
        final Set<FunctionSymbol> constr = this.constructors.get(qdp);
        for (final Rule rule : qdp.getR()) {
            if (rule.getLeft().getRootSymbol().equals(condition) && !rule.getRight().isVariable()) {
                final TRSFunctionApplication rightF = (TRSFunctionApplication) rule.getRight();
                if (((TRSFunctionApplication) rule.getRight()).getRootSymbol().equals(condition)) {
                    // found a rule cond -> cond
                    final int argNum = rule.getLeft().getArguments().size();
                    final Map<Integer, Boolean> contextInformation = new LinkedHashMap<Integer, Boolean>();
                    Formula<None> contextOkFormula = factory.buildConstant(false);
                    for (int i = 0; i < argNum; i++) {
                        if (!this.isConstructorTerm(constr, rule.getLeft().getArgument(i))
                            || !this.isConstructorTerm(constr, rightF.getArgument(i))) {
                            // argument i is no constructor in the left or the right side, so it may not be the ascending/descending argument
                            condToCondFormula =
                                factory.buildAnd(condToCondFormula, factory.buildNot(ascendingInCond.get(i)));
                            condToCondFormula =
                                factory.buildAnd(condToCondFormula, factory.buildNot(descendingInCond.get(i)));
                        } else {
                            // first check if there is a context for position i
                            if ((contextInformation.containsKey(i) && contextInformation.get(i))
                                || this.isContext(rule.getLeft().getArgument(i), rightF.getArgument(i))) {
                                contextInformation.put(i, true);
                                // check for a matching argument more to the right, such that a context can be found (see paper)
                                for (int j = i + 1; j < argNum; j++) {
                                    if ((contextInformation.containsKey(j) && contextInformation.get(j))
                                        || this.isContext(rule.getLeft().getArgument(j), rightF.getArgument(j))) {
                                        contextInformation.put(j, true);
                                        // both positions i, j have a context with K[r|i] = l|i and K'[r|j] = l|j
                                        // now check if there is a single context K for both positions
                                        if (this.singleContext(rule.getLeft().getArgument(i), rightF.getArgument(i),
                                            rule.getLeft().getArgument(j), rightF.getArgument(j))) {
                                            // for the ith and jth argument there is a (single) context, so this pair might be a/d or d/a
                                            contextOkFormula =
                                                factory.buildOr(contextOkFormula,
                                                    factory.buildAnd(ascendingInCond.get(i), descendingInCond.get(j)));
                                            contextOkFormula =
                                                factory.buildOr(contextOkFormula,
                                                    factory.buildAnd(ascendingInCond.get(j), descendingInCond.get(i)));
                                        }
                                    } else {
                                        contextInformation.put(j, false);
                                    }
                                }
                            } else {
                                contextInformation.put(i, false);
                            }
                        }
                    }
                    condToCondFormula = factory.buildAnd(condToCondFormula, contextOkFormula);
                }
            }
        }
        return condToCondFormula;
    }

    private boolean singleContext(final TRSTerm leftDesc, final TRSTerm rightDesc, final TRSTerm leftAsc, final TRSTerm rightAsc) {
        // returns true iff there is a context K with K[rightDesc] = leftDesc and K[rightAsc] = leftAsc
        for (final Pair<Position, TRSTerm> positionAndSubterm : leftDesc.getPositionsWithSubTerms()) {
            if (positionAndSubterm.y.equals(rightDesc)
                && leftDesc.replaceAt(positionAndSubterm.x, rightAsc).equals(leftAsc)) {
                return true;
            }
        }
        return false;
    }

    private Formula<None> buildFormula4(final QDPProblem qdp,
        final FormulaFactory<None> factory,
        final Abortion aborter,
        final List<Rule> condToTrueRules,
        final Rule fToGWithCond,
        final int conditionPosition,
        final Map<FunctionSymbol, List<Variable<None>>> filterArg,
        final Map<FunctionSymbol, List<Variable<None>>> variablesAscending) {
        // for the rule F(..) -> G(..cond(..)..) ensure that the ascending part of the lhs exactly contains one variable
        // then ensure that the ascending part of the rhs is a constructor term only containing the variable of the lhs

        final FunctionSymbol condition = condToTrueRules.get(0).getLeft().getRootSymbol();
        Formula<None> newFormulaAsc = factory.buildConstant(false);
        final FunctionSymbol leftRoot = fToGWithCond.getLeft().getRootSymbol();
        final TRSFunctionApplication rightF = (TRSFunctionApplication) fToGWithCond.getRight();
        final List<Variable<None>> ascLeft = variablesAscending.get(leftRoot);
        final List<Variable<None>> ascCondition = variablesAscending.get(condition);

        // one of the ascending positions (lhs) has to be chosen
        for (int i = 0; i < ascLeft.size(); i++) {
            final TRSTerm termLeft = fToGWithCond.getLeft().getArgument(i);
            if (termLeft.getVariables().size() >= 1) {
                Set<aprove.verification.dpframework.BasicStructures.TRSVariable> vars =
                    new LinkedHashSet<aprove.verification.dpframework.BasicStructures.TRSVariable>();

                final Map<aprove.verification.dpframework.BasicStructures.TRSVariable, Set<Integer>> positionsForVarLeft =
                    new LinkedHashMap<aprove.verification.dpframework.BasicStructures.TRSVariable, Set<Integer>>(0);

                if (termLeft instanceof TRSFunctionApplication) {
                    final TRSFunctionApplication termLeftF = (TRSFunctionApplication) termLeft;
                    vars = termLeft.getVariables();

                    // collect information which subterm contains which variables
                    for (int k = 0; k < termLeftF.getRootSymbol().getArity(); k++) {
                        Set<aprove.verification.dpframework.BasicStructures.TRSVariable> varsInSubterm =
                            new HashSet<aprove.verification.dpframework.BasicStructures.TRSVariable>();
                        varsInSubterm = termLeftF.getArgument(k).getVariables();
                        for (final aprove.verification.dpframework.BasicStructures.TRSVariable var : varsInSubterm) {
                            if (positionsForVarLeft.containsKey(var)) {
                                positionsForVarLeft.get(var).add(k);
                            } else {
                                final Set<Integer> newSet = new LinkedHashSet<Integer>();
                                newSet.add(k);
                                positionsForVarLeft.put(var, newSet);
                            }
                        }
                    }
                } else if (termLeft.isVariable()) {
                    vars = termLeft.getVariables();
                }

                if (Globals.useAssertions) {
                    assert (vars.size() >= 1);
                }

                // now try to find a term in the condition that fits
                for (int j = 0; j < ascCondition.size(); j++) {
                    final TRSFunctionApplication conditionF = (TRSFunctionApplication) rightF.getArgument(conditionPosition);
                    final TRSTerm ascendingInCondition = conditionF.getArgument(j);
                    if (this.isConstructorTerm(this.constructors.get(qdp), ascendingInCondition)
                        && ascendingInCondition.getVariables().size() >= 1) {
                        // this might be a good match, check variable (mind the filtering!)

                        // collect information which subterm contains which variables
                        final Map<aprove.verification.dpframework.BasicStructures.TRSVariable, Set<Integer>> positionsForVarCond =
                            new LinkedHashMap<aprove.verification.dpframework.BasicStructures.TRSVariable, Set<Integer>>(0);

                        if (ascendingInCondition instanceof TRSFunctionApplication) {
                            final TRSFunctionApplication ascendingInConditionF =
                                (TRSFunctionApplication) ascendingInCondition;

                            for (int k = 0; k < ascendingInConditionF.getRootSymbol().getArity(); k++) {
                                Set<aprove.verification.dpframework.BasicStructures.TRSVariable> varsInSubterm =
                                    new HashSet<aprove.verification.dpframework.BasicStructures.TRSVariable>();
                                varsInSubterm = ascendingInConditionF.getArgument(k).getVariables();
                                for (final aprove.verification.dpframework.BasicStructures.TRSVariable varCurrent : varsInSubterm) {
                                    if (positionsForVarCond.containsKey(varCurrent)) {
                                        positionsForVarCond.get(varCurrent).add(k);
                                    } else {
                                        final Set<Integer> newSet = new LinkedHashSet<Integer>();
                                        newSet.add(k);
                                        positionsForVarCond.put(varCurrent, newSet);
                                    }
                                }
                            }
                        }

                        Formula<None> notFiltered = factory.buildConstant(false);

                        for (final aprove.verification.dpframework.BasicStructures.TRSVariable var : vars) {
                            if (positionsForVarCond.containsKey(var)) {
                                // this variable also occurs somewhere in the condition term, good!

                                final TRSFunctionApplication ascendingInConditionF =
                                    (TRSFunctionApplication) ascendingInCondition;

                                for (final Integer pos : positionsForVarCond.get(var)) {
                                    // one of these terms must be not filtered away
                                    // filterList must be ignored, because here the non-flattening version is relevant
                                    notFiltered =
                                        factory.buildOr(notFiltered,
                                            filterArg.get(ascendingInConditionF.getRootSymbol()).get(pos));
                                }

                                Formula<None> otherVariableNotFiltered = factory.buildConstant(false);

                                for (final aprove.verification.dpframework.BasicStructures.TRSVariable varCurrent : vars) {
                                    if (varCurrent != var) {
                                        if (positionsForVarLeft.containsKey(var)) {
                                            final TRSFunctionApplication termLeftF = (TRSFunctionApplication) termLeft;
                                            for (final Integer pos : positionsForVarLeft.get(varCurrent)) {
                                                otherVariableNotFiltered =
                                                    factory.buildOr(otherVariableNotFiltered,
                                                        filterArg.get(termLeftF.getRootSymbol()).get(pos));
                                            }
                                        }
                                    }
                                }

                                // for the current variable:
                                //  - there is some subterm of the condition term containing this variable that is not filtered away
                                //  - all other variables occurring in the left term are filtered away
                                final Variable<None> varLeft = ascLeft.get(i);
                                final Variable<None> varRight = ascCondition.get(j);

                                Formula<None> newSubFormula =
                                    factory.buildAnd(notFiltered, factory.buildNot(otherVariableNotFiltered));
                                newSubFormula = factory.buildAnd(newSubFormula, varLeft, varRight);
                                newFormulaAsc = factory.buildOr(newFormulaAsc, newSubFormula);
                            } else if (ascendingInCondition.isVariable() && ascendingInCondition.equals(var)) {
                                // the term _is_ the variable
                                notFiltered = factory.buildConstant(true);
                                Formula<None> otherVariableNotFiltered = factory.buildConstant(false);

                                for (final aprove.verification.dpframework.BasicStructures.TRSVariable varCurrent : vars) {
                                    if (varCurrent != var) {
                                        if (positionsForVarLeft.containsKey(var)) {
                                            final TRSFunctionApplication termLeftF = (TRSFunctionApplication) termLeft;
                                            for (final Integer pos : positionsForVarLeft.get(varCurrent)) {
                                                otherVariableNotFiltered =
                                                    factory.buildOr(otherVariableNotFiltered,
                                                        filterArg.get(termLeftF.getRootSymbol()).get(pos));
                                            }
                                        }
                                    }
                                }

                                // for the current variable:
                                //  - there is some subterm of the condition term containing this variable that is not filtered away
                                //  - all other variables occurring in the left term are filtered away
                                final Variable<None> varLeft = ascLeft.get(i);
                                final Variable<None> varRight = ascCondition.get(j);

                                Formula<None> newSubFormula =
                                    factory.buildAnd(notFiltered, factory.buildNot(otherVariableNotFiltered));
                                newSubFormula = factory.buildAnd(newSubFormula, varLeft, varRight);
                                newFormulaAsc = factory.buildOr(newFormulaAsc, newSubFormula);
                            }
                        }
                    }
                }
            }
        }
        return newFormulaAsc;
    }

    private Formula<None> buildFormula5(final QDPProblem qdp,
        final FormulaFactory<None> factory,
        final Abortion aborter,
        final List<Rule> condToTrueRules,
        final Rule fToGWithCond,
        final int conditionPosition,
        final Map<FunctionSymbol, List<Variable<None>>> filterArg,
        final Map<FunctionSymbol, List<Variable<None>>> variablesAscending,
        final Map<FunctionSymbol, List<Variable<None>>> variablesDescending,
        final Map<FunctionSymbol, Variable<None>> variableDescendingDummy) {
        // for the rule F(..) -> G(..cond(..)..) ensure that the descending argument of the condition
        // only contains variables of the lhs' descending argument and is a constructor term.
        // This also works if the lhs has no descending argument.
        // Take care that argument filtering may hide some (used or available) variables.

        final FunctionSymbol condition = condToTrueRules.get(0).getLeft().getRootSymbol();
        final FunctionSymbol leftRoot = fToGWithCond.getLeft().getRootSymbol();
        final TRSFunctionApplication rightF = (TRSFunctionApplication) fToGWithCond.getRight();
        final List<Variable<None>> ascLeft = variablesAscending.get(leftRoot);

        Formula<None> newFormulaDesc = factory.buildConstant(false);
        final List<Variable<None>> descLeft = variablesDescending.get(leftRoot);
        final List<Variable<None>> descCondition = variablesDescending.get(condition);
        final TRSFunctionApplication conditionF = (TRSFunctionApplication) rightF.getArgument(conditionPosition);

        // look at all possible descending arguments of the condition
        for (int i = 0; i < descCondition.size(); i++) {
            final TRSTerm termCondition = conditionF.getArgument(i);

            if (this.isConstructorTerm(this.constructors.get(qdp), termCondition)) {
                final Set<aprove.verification.dpframework.BasicStructures.TRSVariable> variablesPossiblyUsed =
                    termCondition.getVariables();

                for (int j = 0; j < ascLeft.size(); j++) {
                    final TRSTerm termLeft = fToGWithCond.getLeft().getArgument(j);

                    // everything looks OK, now ensure that the argument filtering does not filter away needed variables

                    final Map<aprove.verification.dpframework.BasicStructures.TRSVariable, Set<Integer>> positionsForVarCond =
                        new LinkedHashMap<aprove.verification.dpframework.BasicStructures.TRSVariable, Set<Integer>>(0);
                    final Map<aprove.verification.dpframework.BasicStructures.TRSVariable, Set<Integer>> positionsForVarLeft =
                        new LinkedHashMap<aprove.verification.dpframework.BasicStructures.TRSVariable, Set<Integer>>(0);

                    if (termCondition instanceof TRSFunctionApplication) {
                        final TRSFunctionApplication termF = (TRSFunctionApplication) termCondition;
                        final FunctionSymbol termSymbol = termF.getRootSymbol();
                        for (int k = 0; k < termSymbol.getArity(); k++) {
                            final Set<aprove.verification.dpframework.BasicStructures.TRSVariable> varsUsed =
                                termF.getArgument(k).getVariables();
                            for (final aprove.verification.dpframework.BasicStructures.TRSVariable var : varsUsed) {
                                if (positionsForVarCond.containsKey(var)) {
                                    positionsForVarCond.get(var).add(k);
                                } else {
                                    final Set<Integer> newSet = new HashSet<Integer>(1);
                                    newSet.add(k);
                                    positionsForVarCond.put(var, newSet);
                                }
                            }
                        }
                    }

                    // collect information about the variables used on the left side term
                    // remember which subterm of the left term uses which variables
                    // additionally remember which variable is used by which subterms
                    List<Variable<None>> filterVariablesLeft = null;
                    if (termLeft instanceof TRSFunctionApplication) {
                        final TRSFunctionApplication termF = (TRSFunctionApplication) termLeft;
                        final FunctionSymbol termSymbol = termF.getRootSymbol();
                        filterVariablesLeft = filterArg.get(termSymbol);
                        for (int k = 0; k < termSymbol.getArity(); k++) {
                            final Set<aprove.verification.dpframework.BasicStructures.TRSVariable> varsUsed =
                                termF.getArgument(k).getVariables();
                            for (final aprove.verification.dpframework.BasicStructures.TRSVariable var : varsUsed) {
                                if (positionsForVarLeft.containsKey(var)) {
                                    positionsForVarLeft.get(var).add(k);
                                } else {
                                    final Set<Integer> newSet = new HashSet<Integer>(1);
                                    newSet.add(k);
                                    positionsForVarLeft.put(var, newSet);
                                }
                            }
                        }
                    }

                    Formula<None> varsOK = factory.buildConstant(true);
                    Formula<None> noVariableUsed = factory.buildConstant(true);

                    for (final aprove.verification.dpframework.BasicStructures.TRSVariable var : variablesPossiblyUsed) {
                        // this variable is not used because of argument filtering (all subterms using the variable are filtered)
                        // OR
                        // at least one subterm of the condition term is not filtered and provides this variable

                        // the variable is not used iff there is no nonfiltered term that uses the variable (or the term itself is the variable)
                        Formula<None> badPositions = factory.buildConstant(false);
                        if (positionsForVarLeft.containsKey(var)) {
                            for (final int position : positionsForVarLeft.get(var)) {
                                badPositions = factory.buildOr(badPositions, filterVariablesLeft.get(position));
                            }
                        }
                        Formula<None> notUsed = factory.buildNot(badPositions);
                        if (termLeft.isVariable()) {
                            notUsed = factory.buildConstant(false);
                        }
                        noVariableUsed = factory.buildAnd(noVariableUsed, notUsed);

                        Formula<None> varAvailable = factory.buildConstant(false);
                        if (positionsForVarCond.containsKey(var)) {
                            for (final Integer position : positionsForVarCond.get(var)) {
                                final Formula<None> notFiltered = filterArg.get(condition).get(position);
                                varAvailable = factory.buildOr(varAvailable, notFiltered);
                            }
                        }
                        if (termCondition.isVariable() && termCondition.equals(var)) {
                            varAvailable = factory.buildConstant(true);
                        }

                        final Formula<None> newFormula = factory.buildOr(notUsed, varAvailable);
                        varsOK = factory.buildAnd(varsOK, newFormula);
                    }

                    // additionally handle the case that the left term has no descending argument
                    final Formula<None> noDescArgument = variableDescendingDummy.get(leftRoot);
                    final Formula<None> alternative = factory.buildAnd(noVariableUsed, noDescArgument);

                    final Variable<None> varCondition = descCondition.get(i);
                    final Variable<None> varLeft = descLeft.get(j);

                    final Formula<None> newFormula = factory.buildAnd(varLeft, varCondition, varsOK);

                    newFormulaDesc = factory.buildOr(newFormulaDesc, alternative, newFormula);
                }
            }
        }
        return newFormulaDesc;
    }

    private void getUsableRules(final QDPProblem qdp,
        final Map<Rule, QActiveCondition> activeConds,
        final Map<FunctionSymbol, List<Variable<None>>> variablesAsc,
        final Map<FunctionSymbol, List<Variable<None>>> variablesDesc,
        final FormulaFactory<None> factory,
        final Map<FunctionSymbol, Variable<None>> filterList,
        final Map<FunctionSymbol, List<Variable<None>>> filterArg,
        final Map<Variable<None>, String> variableToString,
        final Set<Pair<Formula<None>, Rule>> usableRulesAsc,
        final Set<Pair<Formula<None>, Rule>> usableRulesDesc) {

        for (final Map.Entry<Rule, QActiveCondition> entry : activeConds.entrySet()) {
            final Rule rule = entry.getKey();
            final QActiveCondition activeCond = entry.getValue();
            Formula<None> outerFormulaAsc = factory.buildConstant(false);
            Formula<None> outerFormulaDesc = factory.buildConstant(false);
            for (final Set<Pair<FunctionSymbol, Integer>> poss : activeCond.getSetRepresentation()) {
                Formula<None> innerFormulaAsc = factory.buildConstant(true);
                Formula<None> innerFormulaDesc = factory.buildConstant(true);
                for (final Pair<FunctionSymbol, Integer> pos : poss) {
                    final FunctionSymbol symbol = pos.x;

                    if (!filterList.containsKey(symbol)) {
                        final Variable<None> listVar = factory.buildVariable();
                        variableToString.put(listVar, "The symbol '" + symbol + "' is filtered to a list.");
                        filterList.put(symbol, listVar);
                        final List<Variable<None>> argVars = factory.buildVariables(symbol.getArity());
                        for (int i = 0; i < symbol.getArity(); i++) {
                            variableToString.put(argVars.get(i), "The argument #" + (i + 1) + " of symbol '" + symbol
                                + "' is not filtered.");
                        }
                        filterArg.put(symbol, argVars);
                    }

                    final Integer position = pos.y;
                    Formula<None> positionAscOk = factory.buildConstant(true);
                    Formula<None> positionDescOk = factory.buildConstant(true);
                    if (variablesAsc.containsKey(symbol)) {
                        positionAscOk = variablesAsc.get(symbol).get(position);
                        positionDescOk = variablesDesc.get(symbol).get(position);
                    }
                    final Variable<None> positionNotFiltered = filterArg.get(symbol).get(position);
                    final Formula<None> okAsc = factory.buildAnd(positionNotFiltered, positionAscOk);
                    final Formula<None> okDesc = factory.buildAnd(positionNotFiltered, positionDescOk);
                    innerFormulaAsc = factory.buildAnd(innerFormulaAsc, okAsc);
                    innerFormulaDesc = factory.buildAnd(innerFormulaDesc, okDesc);
                }
                outerFormulaAsc = factory.buildOr(outerFormulaAsc, innerFormulaAsc);
                outerFormulaDesc = factory.buildOr(outerFormulaDesc, innerFormulaDesc);
            }
            usableRulesAsc.add(new Pair<Formula<None>, Rule>(outerFormulaAsc, rule));
            usableRulesDesc.add(new Pair<Formula<None>, Rule>(outerFormulaDesc, rule));
        }
    }

    private Variable<None> getFromConstraintMap(final Map<Constraint<TRSTerm>, Variable<None>> constraintMap,
        final Constraint<TRSTerm> constraint,
        final FormulaFactory<None> factory,
        final Map<Variable<None>, String> variableToString) {
        if (!constraintMap.containsKey(constraint)) {
            final Variable<None> var = factory.buildVariable();
            constraintMap.put(constraint, var);
            variableToString.put(var, "The constraint '" + constraint + "' is fulfilled.");
        }
        return constraintMap.get(constraint);
    }

    private BasicObligation getQdpWithoutP(final QDPProblem qdp) {
        return qdp.getSubProblem(ImmutableCreator.create(new LinkedHashSet<Rule>(0)));
    }

    private boolean findBadRules(final QDPProblem qdp, final FunctionSymbol conditionSymbol) {
        final Set<Rule> rules = qdp.getR();
        // scan all rules and find cond() -> .. where .. is not a constructor (e.g. true) and not cond(..)
        for (final Rule rule : rules) {
            if (rule.getLeft().getRootSymbol().equals(conditionSymbol)) {
                if (rule.getRight().isVariable()) {
                    return true; // found cond()->x
                } else if (!this.isConstructorTerm(this.constructors.get(qdp), rule.getRight())
                    && !((TRSFunctionApplication) rule.getRight()).getRootSymbol().equals(conditionSymbol)) {
                    return true; // found cond()->something (where something is not a constructor and not cond())
                }
            }
        }
        return false;
    }

    private boolean isConstructorTerm(final Set<FunctionSymbol> constr, final TRSTerm term) {
        if (term.isVariable()) {
            return true;
        } else {
            final TRSFunctionApplication termF = (TRSFunctionApplication) term;
            return constr.contains(termF.getRootSymbol());
        }
    }

    private boolean isContext(final TRSTerm argument, final TRSTerm argument2) {
        // is there a context C such that C[arg2] = arg?
        return (argument.getSubTerms().contains(argument2));
    }

    private List<Rule> findToTrueRules(final QDPProblem qdp, final TRSTerm condition, final TRSTerm trueArgument) {
        // returns the (single) rule that does cond(..) -> true (with previously found "cond" and "true")
        final List<Rule> foundRules = new LinkedList<Rule>();
        final FunctionSymbol conditionFunction = ((TRSFunctionApplication) condition).getRootSymbol();
        for (final Rule rule : qdp.getR()) {
            if (rule.getLeft().getRootSymbol().equals(conditionFunction) && rule.getRight().equals(trueArgument)) {
                foundRules.add(rule);
            }
        }
        return foundRules;
    }

    private Formula<None> buildGr(final TRSTerm left,
        final TRSTerm right,
        final FormulaFactory<None> factory,
        final Map<FunctionSymbol, List<Variable<None>>> filterArg,
        final Map<FunctionSymbol, Variable<None>> filterList,
        final Map<Variable<None>, Fact> poConstraints,
        final Map<Variable<None>, String> variableToString) {
        if (!(left instanceof TRSFunctionApplication)) {
            return factory.buildConstant(false);
        }
        final TRSFunctionApplication leftF = (TRSFunctionApplication) left;
        final FunctionSymbol symbolLeft = leftF.getRootSymbol();

        Formula<None> newFormula1a = factory.buildConstant(false);
        Formula<None> newFormula1b = factory.buildConstant(false);
        Formula<None> newFormula2 = factory.buildConstant(false);

        Formula<None> firstOr = factory.buildConstant(false);
        for (int i = 0; i < symbolLeft.getArity(); i++) {
            final Formula<None> first = filterArg.get(symbolLeft).get(i);
            final Formula<None> second =
                this.buildGr(leftF.getArgument(i), right, factory, filterArg, filterList, poConstraints, variableToString);
            final Formula<None> andFormula = factory.buildAnd(first, second);
            firstOr = factory.buildOr(firstOr, andFormula);
        }

        final Formula<None> leftNotCollapsing = filterList.get(symbolLeft);
        Formula<None> secondOr = factory.buildConstant(false);
        for (int i = 0; i < symbolLeft.getArity(); i++) {
            final Formula<None> argumentNotFiltered = filterArg.get(symbolLeft).get(i);
            Formula<None> smallerLPO;
            if (leftF.getArgument(i).equals(right)) {
                smallerLPO = factory.buildConstant(true);
            } else {
                smallerLPO =
                    this.buildGr(leftF.getArgument(i), right, factory, filterArg, filterList, poConstraints,
                        variableToString);
            }
            secondOr = factory.buildOr(secondOr, factory.buildAnd(argumentNotFiltered, smallerLPO));
        }

        newFormula2 = factory.buildOr(firstOr, factory.buildAnd(leftNotCollapsing, secondOr));

        if (right instanceof TRSFunctionApplication) {
            // tau_1a from "SAT Solving for Argument Filterings" page 8
            final TRSFunctionApplication rightF = (TRSFunctionApplication) right;
            final FunctionSymbol symbolRight = rightF.getRootSymbol();
            final Formula<None> collapsing = factory.buildNot(filterList.get(symbolRight));
            Formula<None> tempFormula = factory.buildConstant(false);
            for (int i = 0; i < symbolRight.getArity(); i++) {
                final Formula<None> containsI = filterArg.get(symbolRight).get(i);
                final Formula<None> smallerLPO =
                    this.buildGr(left, rightF.getArgument(i), factory, filterArg, filterList, poConstraints,
                        variableToString);
                tempFormula = factory.buildOr(tempFormula, factory.buildAnd(containsI, smallerLPO));
            }
            newFormula1a = factory.buildAnd(collapsing, tempFormula);

            // tau_1b from same paper same page
            if (!symbolLeft.equals(symbolRight)) {
                final Formula<None> rightNotCollapsing = filterList.get(rightF.getRootSymbol());

                final Variable<None> leftSymbolGrRightSymbol = factory.buildVariable();
                final Fact fact = new FactSucc(leftF.getRootSymbol(), rightF.getRootSymbol());
                variableToString.put(leftSymbolGrRightSymbol, "The fact '" + fact + "' is fulfilled.");
                poConstraints.put(leftSymbolGrRightSymbol, fact);

                tempFormula = factory.buildConstant(true);
                for (int j = 0; j < symbolRight.getArity(); j++) {
                    final Formula<None> argInList = filterArg.get(symbolRight).get(j);
                    final Formula<None> smallerLPO =
                        this.buildGr(left, rightF.getArgument(j), factory, filterArg, filterList, poConstraints,
                            variableToString);
                    final Formula<None> implication = factory.buildImplication(argInList, smallerLPO);
                    tempFormula = factory.buildAnd(tempFormula, implication);
                }
                newFormula1b = factory.buildAnd(leftNotCollapsing, rightNotCollapsing, leftSymbolGrRightSymbol);
                newFormula1b = factory.buildAnd(newFormula1b, tempFormula);
            } else {
                final Formula<None> encodingII =
                    this.buildEncodingII(leftF, rightF, 0, factory, filterArg, filterList, poConstraints, variableToString);
                tempFormula = factory.buildConstant(true);
                final int arity = symbolLeft.getArity();
                for (int i = 0; i < arity; i++) {
                    final Formula<None> first = filterArg.get(symbolLeft).get(i);
                    final Formula<None> second =
                        this.buildGr(left, rightF.getArgument(i), factory, filterArg, filterList, poConstraints,
                            variableToString);
                    final Formula<None> implication = factory.buildImplication(first, second);
                    tempFormula = factory.buildAnd(tempFormula, implication);
                }
                newFormula1b = factory.buildAnd(leftNotCollapsing, encodingII, tempFormula);
            }
        }

        final Formula<None> newFormula = factory.buildOr(newFormula1a, newFormula1b, newFormula2);
        return newFormula;
    }

    private Formula<None> buildEncodingII(final TRSFunctionApplication leftF,
        final TRSFunctionApplication rightF,
        final int start,
        final FormulaFactory<None> factory,
        final Map<FunctionSymbol, List<Variable<None>>> filterArg,
        final Map<FunctionSymbol, Variable<None>> filterList,
        final Map<Variable<None>, Fact> poConstraints,
        final Map<Variable<None>, String> variableToString) {
        final int arity = leftF.getRootSymbol().getArity();

        if (Globals.useAssertions) {
            assert (start <= arity);
        }

        final FunctionSymbol symbol = leftF.getRootSymbol();
        if (arity == 0) {
            return factory.buildConstant(false);
        } else {
            final Formula<None> startNotFiltered = filterArg.get(symbol).get(start);
            final Formula<None> smallerLPO =
                this.buildGr(leftF.getArgument(start), rightF.getArgument(start), factory, filterArg, filterList,
                    poConstraints, variableToString);
            Formula<None> formulaGe;
            if (leftF.getArgument(start).equals(rightF.getArgument(start))) {
                formulaGe = factory.buildConstant(true);
            } else {
                formulaGe = smallerLPO;
            }
            Formula<None> encodingII;
            if (start + 1 < arity) {
                encodingII =
                    this.buildEncodingII(leftF, rightF, start + 1, factory, filterArg, filterList, poConstraints,
                        variableToString);
            } else {
                encodingII = factory.buildConstant(false);
            }
            final Formula<None> implication = factory.buildImplication(startNotFiltered, formulaGe);
            final Formula<None> firstPart = factory.buildAnd(startNotFiltered, smallerLPO);
            final Formula<None> secondPart = factory.buildAnd(implication, encodingII);
            return factory.buildOr(firstPart, secondPart);
        }
    }

    private void log(final Level level, final String string) {
        if (QDPBoundedIncreaseProcessor.logger.isLoggable(level)) {
            QDPBoundedIncreaseProcessor.logger.log(level, string);
        }
    }

    public ExportableOrder<TRSTerm> getPoSet(final Map<Variable<None>, Fact> factMap, final int[] result) {
        final Set<FunctionSymbol> symbols = new LinkedHashSet<FunctionSymbol>();
        final int max = result.length;
        for (final Map.Entry<Variable<None>, Fact> e : factMap.entrySet()) {
            final Variable<None> var = e.getKey();
            final int varId = var.getId();
            if (varId >= 0 && varId <= max && result[varId - 1] == varId) {
                final Fact fact = e.getValue();
                if (fact instanceof FactBot) {
                    final FactBot factBot = (FactBot) fact;
                    symbols.add(factBot.getFunctionSymbol());
                } else if (fact instanceof FactSucc) {
                    final FactSucc factSucc = (FactSucc) fact;
                    symbols.add(factSucc.getLeft());
                    symbols.add(factSucc.getRight());
                }
            }
        }

        final Poset<FunctionSymbol> poset = Poset.create(symbols);

        try {
            for (final Map.Entry<Variable<None>, Fact> e : factMap.entrySet()) {
                final Variable<None> var = e.getKey();
                final int varId = var.getId();
                if (varId >= 0 && varId <= max && result[varId - 1] == varId) {
                    final Fact fact = e.getValue();
                    if (fact instanceof FactBot) {
                        final FactBot factBot = (FactBot) fact;
                        final FunctionSymbol symbol = factBot.getFunctionSymbol();
                        poset.setMinimal(symbol);
                    } else if (fact instanceof FactSucc) {
                        final FactSucc factSucc = (FactSucc) fact;
                        final FunctionSymbol left = factSucc.getLeft();
                        final FunctionSymbol right = factSucc.getRight();
                        poset.setGreater(left, right);
                    }
                }
            }
        } catch (final OrderedSetException e) {
            e.printStackTrace();
            if (Globals.useAssertions) {
                assert false : e.getMessage();
            }
        }
        return LPO.create(poset);
    }

    public void calculateConstructors(final QDPProblem qdp) {
        if (this.constructors.get(qdp) == null) {
            // only synchronize if cache is not yet computed,
            // synchronize to omit multiple computation
            synchronized (this.constructorsLock) {
                if (this.constructors.get(qdp) == null) {
                    final Set<FunctionSymbol> defSymbols = new LinkedHashSet<FunctionSymbol>(0);
                    this.definedSymbols.put(qdp, defSymbols);
                    final Set<FunctionSymbol> constr = new LinkedHashSet<FunctionSymbol>(0);
                    this.constructors.put(qdp, constr);

                    final Set<Rule> rules = qdp.getR();
                    for (final Rule rule : rules) {
                        this.definedSymbols.get(qdp).add(rule.getLeft().getRootSymbol());
                    }
                    for (final Rule rule : rules) {
                        for (final FunctionSymbol functionSymbol : rule.getFunctionSymbols()) {
                            if (!this.definedSymbols.get(qdp).contains(functionSymbol)) {
                                this.constructors.get(qdp).add(functionSymbol);
                            }
                        }
                    }
                }
            }
        }
    }

    private class BoundedIncreaseProof extends Proof.DefaultProof {

        QDPProblem qdp;
        String text = "";

        private BoundedIncreaseProof(final QDPProblem qdp, final String text) {
            this.qdp = qdp;
            this.text = text;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            return this.text;
        }
    }

}
