package aprove.input.Programs.prolog.graph;

import java.util.*;

import org.json.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.graph.rules.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.JSON.*;

/**
 * Symbolic evaluation graph for Prolog programs.<br><br>
 *
 * Created: Dec 1, 2006<br>
 * Last modified: Aug 19, 2015
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologEvaluationGraph extends Graph<PrologAbstractState, AbstractInferenceRule> {

//    private static boolean fixpointDebug = true; // DEBUG STUFF

    private static final boolean META = true;

    private static final long serialVersionUID = 4284139970981642832L;

    /**
     * Factory to build SMT solvers.
     */
    private final SMTSolverFactory smtFactory;

    /**
     * Logic for SMT solvers.
     */
    private final SMTLIBLogic smtLogic;

    public static PrologSubstitution calculateMGUConsideringFreeVariables(
        PrologTerm term1,
        PrologTerm term2,
        KnowledgeBase kb
    ) {
        PrologSubstitution res = new PrologSubstitution();
        if (term1.isVariable()) {
            if (term2.isVariable()) {
                if (term1.equals(term2)) {
                    return res;
                } else {
                    if (term1.isAbstractVariable()) {
                        res.put((PrologVariable) term2, term1);
                    } else if (!term1.isAbstractVariable() && term2.isAbstractVariable()) {
                        res.put((PrologVariable) term1, term2);
                    } else if (kb.isFree((PrologNonAbstractVariable) term1)) {
                        res.put((PrologVariable) term2, term1);
                    } else {
                        res.put((PrologVariable) term1, term2);
                    }
                    return res;
                }
            } else {
                if (!term2.occurs(term1)) {
                    res.put((PrologVariable) term1, term2);
                    return res;
                }
            }
        } else if (term2.isVariable()) {
            if (!term1.occurs(term2)) {
                res.put((PrologVariable) term2, term1);
                return res;
            }
        } else if (term1.getName().equals(term2.getName()) && term1.getArity() == term2.getArity()) {
            // corresponds to equal function symbols, i.e.,
            // term1.createFunctionSymbol().equals(term2.createFunctionSymbol())
            for (int i = 0; i < term1.getArity(); i++) {
                Map<PrologVariable, PrologTerm> mgu =
                    PrologEvaluationGraph.calculateMGUConsideringFreeVariables(
                        term1.getArgument(i),
                        term2.getArgument(i),
                        kb);
                if (mgu == null) {
                    return null;
                } else {
                    // replaces the terms immediately to avoid
                    // clashes in substitutions
                    Pair<PrologTerm, PrologTerm> pair =
                        PrologEvaluationGraph.combineMGUforArguments(term1, term2, i, mgu, res);
                    term1 = pair.x;
                    term2 = pair.y;
                }
            }
            return res;
        }
        return null;
    }

    /**
     * Checks the specified substitution for compatibility with a backtrack case. This is the case whenever an abstract
     * variable is replaced by something else than another abstract variable or when two different abstract variables
     * are replaced by the same abstract variable.
     * @param sigma The substitution to check.
     * @return True if the specified substitution may include a backtrack case.
     */
    public static boolean checkForBacktrack(Map<PrologVariable, PrologTerm> sigma) {
        Set<PrologAbstractVariable> used = new LinkedHashSet<PrologAbstractVariable>();
        for (Map.Entry<PrologVariable, PrologTerm> entry : sigma.entrySet()) {
            if (entry.getKey().isAbstractVariable()) {
                if (entry.getValue().isAbstractVariable()) {
                    if (used.contains(entry.getValue())) {
                        return true;
                    } else {
                        used.add((PrologAbstractVariable) entry.getValue());
                    }
                } else {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * The transformation of a problem into a starting state is defined in {@link PrologEvaluationGraph#transformQuery(PrologQuery, FreshNameGenerator)}
     * @param obl Some prolog problem. Must not be null.
     * @return A new graph containing only the starting state for the given problem.
     */
    public static PrologEvaluationGraph create(PrologProblem obl) {
        PrologProgram program = obl.getProgram();
        Set<String> used = program.createSetOfAllSymbolNames();
        used.add("X");
        used.add("X0");
        used.add("T");
        used.add("T0");
        FreshNameGenerator fridge = new FreshNameGenerator(used, FreshNameGenerator.PROLOG_VARS);
        final int scope = 1;
        Triple<PrologTerm, Set<PrologAbstractVariable>, Set<PrologAbstractVariable>> triple =
            PrologEvaluationGraph.transformQuery(obl.getQuery(), fridge);
        Map<PrologAbstractVariable, PrologInterval> numbers =
            new LinkedHashMap<PrologAbstractVariable, PrologInterval>();
        for (PrologAbstractVariable v : triple.z) {
            numbers.put(v, new PrologInterval());
        }
        final Node<PrologAbstractState> rootNode =
            PrologEvaluationGraph.createCleanedNode(
                PrologAbstractState.createFromTerm(
                    triple.x,
                    KnowledgeBase.createWithGroundAndIntegers(triple.y, numbers, obl.getSMTFactory(), obl.getSMTLogic())
                )
            );
        PrologEvaluationGraph returnValue =
            new PrologEvaluationGraph(fridge, program, rootNode, scope, obl.getSMTFactory(), obl.getSMTLogic());
        returnValue.addNode(rootNode);
        return returnValue;
    }

    /**
     * A state is cleaned by removing all its trailing question marks
     * @param pet Some abstract state
     * @return A node containing a cleaned version of the given state pet
     */
    public static Node<PrologAbstractState> createCleanedNode(PrologAbstractState pet) {
        List<GoalElement> state = new ArrayList<GoalElement>(pet.getState());
        //        Set<Integer> ac = this.calculateActiveCuts(state);
        Set<GoalElement> toDelete = new LinkedHashSet<GoalElement>();
        for (int i = state.size() - 1; i >= 0 && state.get(i).isQuestionMark(); i--) {
            toDelete.add(state.get(i));
        }
        state.removeAll(toDelete);
        return new Node<PrologAbstractState>(PrologAbstractState.createCleanedState(pet.replaceState(state)));
    }

    public static PrologTerm transformed(PrologTerm term, int scope) {
        if (term == null) {
            return null;
        }
        if (term.isNonAbstractVariable()) {
            return PrologTerms.createCall(term);
        }
        if (term.isCut()) {
            return new LabeledCut(scope);
        }
        if (term.isConjunction()) {
            return PrologTerms.createConjunction(
                PrologEvaluationGraph.transformed(term.getArgument(0), scope),
                PrologEvaluationGraph.transformed(term.getArgument(1), scope));
        }
        if (term.isDisjunctionTerm()) {
            return PrologTerms.createDisjunction(
                PrologEvaluationGraph.transformed(term.getArgument(0), scope),
                PrologEvaluationGraph.transformed(term.getArgument(1), scope));
        }
        if (term.isIf()) {
            return PrologTerms.createIf(
                PrologEvaluationGraph.transformed(term.getArgument(0), scope),
                PrologEvaluationGraph.transformed(term.getArgument(1), scope));
        }
        return term;
    }

    /**
     * @param term
     * @param position
     * @param symbolCount
     * @param firstOccurence
     * @param res
     */
    private static void calculateGeneralizationPositions(
        int maxNestedDepth,
        boolean generalizeAtFirstOccurence,
        PrologTerm originalTerm,
        PrologTerm term,
        Occurrence position,
        Map<FunctionSymbol, Integer> symbolCount,
        Map<FunctionSymbol, Occurrence> firstOccurence,
        Set<Occurrence> res
    ) {
        final FunctionSymbol symbol = term.createFunctionSymbol();
        if (firstOccurence.containsKey(symbol)) {
            final Integer count = symbolCount.get(symbol);
            final int limit = maxNestedDepth - 1;
            if (!symbol.equals(PrologBuiltin.CONJUNCTION_PREDICATE) && count > limit) {
                if (generalizeAtFirstOccurence) {
                    final Occurrence firstPos = firstOccurence.get(symbol);
                    final PrologTerm subTerm = originalTerm.getSubterm(firstPos);
                    for (int i = 0; i < subTerm.getArity(); i++) {
                        res.add(firstPos.appendChildNumber(i));
                    }
                    PrologEvaluationGraph.calculateGeneralizationPositionsForChildren(
                        maxNestedDepth,
                        generalizeAtFirstOccurence,
                        originalTerm,
                        term,
                        position,
                        symbolCount,
                        firstOccurence,
                        res);
                } else {
                    res.add(position);
                }
            } else {
                symbolCount.put(symbol, Integer.valueOf(count + 1));
                PrologEvaluationGraph.calculateGeneralizationPositionsForChildren(
                    maxNestedDepth,
                    generalizeAtFirstOccurence,
                    originalTerm,
                    term,
                    position,
                    symbolCount,
                    firstOccurence,
                    res);
                symbolCount.put(symbol, count);
            }
        } else {
            firstOccurence.put(symbol, position);
            symbolCount.put(symbol, Integer.valueOf(1));
            PrologEvaluationGraph.calculateGeneralizationPositionsForChildren(
                maxNestedDepth,
                generalizeAtFirstOccurence,
                originalTerm,
                term,
                position,
                symbolCount,
                firstOccurence,
                res);
            firstOccurence.remove(symbol);
            symbolCount.remove(symbol);
        }
    }

    /**
     * Calculates a set of Occurences where the specified term can
     * generalized according to the specified maximum nested depth
     * and generalization depth.
     * @param term The term to generalize.
     * @param maxNestedDepth The maximum nested depth.
     * @param generalizationDepth The generalization depth.
     * @return A set of Occurences where the specified term can be
     *         generalized.
     */
    private static Set<Occurrence> calculateGeneralizationPositions(
        PrologTerm term,
        int maxNestedDepth,
        boolean generalizeAtFirstOccurence
    ) {
        Set<Occurrence> res = new LinkedHashSet<Occurrence>();
        PrologEvaluationGraph.calculateGeneralizationPositions(
            maxNestedDepth,
            generalizeAtFirstOccurence,
            term,
            term,
            new Occurrence(),
            new LinkedHashMap<FunctionSymbol, Integer>(),
            new LinkedHashMap<FunctionSymbol, Occurrence>(),
            res
        );
        Occurrence.reduceToSmallest(res);
        return res;
    }

    /**
     * @param originalTerm
     * @param term
     * @param symbolCount
     * @param firstOccurence
     * @param res
     */
    private static void calculateGeneralizationPositionsForChildren(
        int generalizationDepth,
        boolean generalizeAtFirstOccurence,
        PrologTerm originalTerm,
        PrologTerm term,
        Occurrence position,
        Map<FunctionSymbol, Integer> symbolCount,
        Map<FunctionSymbol, Occurrence> firstOccurence,
        Set<Occurrence> res
    ) {
        for (int i = 0; i < term.getArity(); i++) {
            PrologEvaluationGraph.calculateGeneralizationPositions(
                generalizationDepth,
                generalizeAtFirstOccurence,
                originalTerm,
                term.getArgument(i),
                position.appendChildNumber(i),
                symbolCount,
                firstOccurence,
                res
            );
        }
    }

    /**
     * Combines the replacements of the new argument MGU and the
     * current complete MGU and performs the replacements in the
     * terms immediately. Thus, clashes can be detected in the
     * replaced terms instead of different replacements in
     * argument MGUs.
     * @param term1
     * @param term2
     * @param i
     * @param mgu
     * @param res
     */
    private static Pair<PrologTerm, PrologTerm> combineMGUforArguments(
        PrologTerm term1,
        PrologTerm term2,
        int i,
        Map<PrologVariable, PrologTerm> mgu,
        Map<PrologVariable, PrologTerm> res
    ) {
        Pair<PrologTerm, PrologTerm> pair = new Pair<PrologTerm, PrologTerm>(term1, term2);
        for (Map.Entry<PrologVariable, PrologTerm> entry : mgu.entrySet()) {
            for (Map.Entry<PrologVariable, PrologTerm> e : res.entrySet()) {
                if (e.getValue().equals(entry.getKey())) {
                    res.put(e.getKey(), entry.getValue());
                } else {
                    res.put(e.getKey(), e.getValue().replaceAll(entry.getKey(), entry.getValue()));
                }
            }
            res.put(entry.getKey(), entry.getValue());
            pair.x = pair.x.replaceAll(entry.getKey(), entry.getValue());
            pair.y = pair.y.replaceAll(entry.getKey(), entry.getValue());
        }
        return pair;
    }

    private static boolean equalityYieldsTrue(FunctionSymbol sym) {
        return
            PrologBuiltin.ISEQUAL_PREDICATE.equals(sym)
            || PrologBuiltin.GEQ_PREDICATE.equals(sym)
            || PrologBuiltin.LEQ_PREDICATE.equals(sym);
    }

    private static PrologInterval evaluate(PrologTerm expr, KnowledgeBase kb) {
        if (expr.isInt()) {
            return new PrologInterval(((PrologInt) expr).getValue());
        } else if (expr.isNumber()) {
            return null;
        } else if (expr.isAbstractVariable()) {
            if (kb.isNumber(expr)) {
                return kb.getIntegerMap().get(expr);
            } else {
                // it might be a float...
                return null;
            }
        } else {
            // we must have an arithmetic operator
            final FunctionSymbol sym = expr.createFunctionSymbol();
            if (sym.equals(PrologBuiltin.PLUS_SYMBOL)) {
                final PrologInterval arg1 = PrologEvaluationGraph.evaluate(expr.getArgument(0), kb);
                if (arg1 == null) {
                    return null;
                }
                final PrologInterval arg2 = PrologEvaluationGraph.evaluate(expr.getArgument(1), kb);
                if (arg2 == null) {
                    return null;
                }
                return arg1.plus(arg2);
            } else if (sym.equals(PrologBuiltin.MINUS_SYMBOL)) {
                final PrologInterval arg1 = PrologEvaluationGraph.evaluate(expr.getArgument(0), kb);
                if (arg1 == null) {
                    return null;
                }
                final PrologInterval arg2 = PrologEvaluationGraph.evaluate(expr.getArgument(1), kb);
                if (arg2 == null) {
                    return null;
                }
                return arg1.minus(arg2);
            } else if (sym.equals(PrologBuiltin.TIMES_SYMBOL)) {
                final PrologInterval arg1 = PrologEvaluationGraph.evaluate(expr.getArgument(0), kb);
                if (arg1 == null) {
                    return null;
                }
                final PrologInterval arg2 = PrologEvaluationGraph.evaluate(expr.getArgument(1), kb);
                if (arg2 == null) {
                    return null;
                }
                return arg1.times(arg2);
            } else if (sym.equals(PrologBuiltin.INTDIV_SYMBOL)) {
                final PrologInterval arg1 = PrologEvaluationGraph.evaluate(expr.getArgument(0), kb);
                if (arg1 == null) {
                    return null;
                }
                final PrologInterval arg2 = PrologEvaluationGraph.evaluate(expr.getArgument(1), kb);
                if (arg2 == null) {
                    return null;
                }
                return arg1.intdiv(arg2);
            } else if (sym.equals(PrologBuiltin.POSITIVE_SIGN)) {
                return PrologEvaluationGraph.evaluate(expr.getArgument(0), kb);
            } else if (sym.equals(PrologBuiltin.NEGATIVE_SIGN)) {
                final PrologInterval arg = PrologEvaluationGraph.evaluate(expr.getArgument(0), kb);
                if (arg == null) {
                    return null;
                }
                return arg.negate();
            } else {
                return null;
            }
        }
    }

    private static boolean isArithmeticExpression(PrologTerm expr) {
        if (expr.getArity() == 0) {
            return expr.isNumber() || expr.isAbstractVariable();
        }
        if (!PrologBuiltins.ARITHMETIC_OPERATORS.contains(expr.createFunctionSymbol())) {
            return false;
        }
        for (PrologTerm child : expr.getArguments()) {
            if (!PrologEvaluationGraph.isArithmeticExpression(child)) {
                return false;
            }
        }
        return true;
    }

    /**
     * May only be called for equal expressions or concrete intervals.
     * @param expr1
     * @param expr2
     * @param value1
     * @param value2
     * @return
     */
    private static boolean isDefinitelyEqual(
        PrologTerm expr1,
        PrologTerm expr2,
        PrologInterval value1,
        PrologInterval value2
    ) {
        return expr1.equals(expr2) || value1.getLower().compareTo(value2.getLower()) == 0;
    }

    /**
     * Transforms a query into a PrologTerm and a set of variables
     * considered to be ground or numbers.
     * @param query The query.
     * @return A term and two sets of variables representing the same query. None of these are ever null.
     */
    private static Triple<PrologTerm, Set<PrologAbstractVariable>, Set<PrologAbstractVariable>> transformQuery(
        PrologQuery query,
        FreshNameGenerator fng
    ) {
        final Set<PrologAbstractVariable> moding = new LinkedHashSet<PrologAbstractVariable>();
        final Set<PrologAbstractVariable> numbers = new LinkedHashSet<PrologAbstractVariable>();
        final List<PrologTerm> args = new ArrayList<PrologTerm>();
        final Moding[] mode = query.getModing();
        for (int j = 0; j < query.getArity(); j++) {
            final PrologAbstractVariable t = new PrologAbstractVariable(fng.getFreshName("T", false));
            args.add(t);
            switch (mode[j]) {
            case NUMBER:
                numbers.add(t);
            case GROUND:
                moding.add(t);
            default:
                // do nothing
            }
        }
        return
            new Triple<PrologTerm, Set<PrologAbstractVariable>, Set<PrologAbstractVariable>>(
                new PrologTerm(query.getName(), args),
                moding,
                numbers
            );
    }

    private FreshNameGenerator fridge;

    private PrologProgram program;

    private Node<PrologAbstractState> root;

    private int scope;

    /**
     * @param queries
     * @param program
     * @param factory Factory to build SMT solvers.
     */
    protected PrologEvaluationGraph(
        FreshNameGenerator fridge,
        PrologProgram program,
        Node<PrologAbstractState> root,
        int scope,
        SMTSolverFactory factory,
        SMTLIBLogic logic
    ) {
        this.fridge = fridge;
        this.program = program;
        this.root = root;
        this.scope = scope;
        this.smtFactory = factory;
        this.smtLogic = logic;
    }

    public Set<Integer> calculateActiveCuts(List<GoalElement> state) {
        final Set<Integer> ac = new LinkedHashSet<Integer>();
        TermWalker walker = new TermWalker() {

            @Override
            public boolean goDeeper(PrologTerm term) {
                return true;
            }

            @Override
            public boolean isApplicable(PrologTerm term) {
                return term instanceof LabeledCut;
            }

            @Override
            public void performAction(PrologTerm term) {
                ac.add(((LabeledCut) term).getNumber());
            }

        };
        for (int i = 0; i < state.size(); i++) {
            final GoalElement e = state.get(i);
            if (!e.isQuestionMark()) {
                e.getTerm().walkConjunction(walker);
                if (e.hasApplicableClause()) {
                    final PrologTerm body = this.getProgram().getClause(e.getApplicableClause()).getBody();
                    if (body != null && body.containsCut()) {
                        ac.add(e.getScope());
                    }
                }
            }
        }
        return ac;
    }

    public PrologSubstitution calculateMGUwithOnlyFreshVariables(PrologTerm t, PrologTerm h) {
        return t.calculateMGUwithOnlyFreshVariables(h, this.getFNG());
    }

    /**
     * Computes reachability in this graph.
     * @param node The start node to consider.
     * @param target The target node to consider.
     * @param aborter For abortions...
     * @return True if <code>node</code> can reach <code>target</code> in
     *         this graph via a non-empty path.
     * @throws AbortionException If it is aborted...
     */
    public boolean canReachNode(Node<PrologAbstractState> node, Node<PrologAbstractState> target, Abortion aborter)
    throws AbortionException {
        return this.canReachNode(node, target, new LinkedHashSet<Node<PrologAbstractState>>(), aborter);
    }

    /**
     * Computes reachability of any SUCCESS node.
     * @param node The start node to consider.
     * @param aborter For abortions...
     * @return True if <code>node</code> can reach any SUCCESS node in
     *         this graph.
     * @throws AbortionException If it is aborted...
     */
    public boolean canReachSuccess(Node<PrologAbstractState> node, Abortion aborter) throws AbortionException {
        return this.canReachSuccess(node, new LinkedHashSet<Node<PrologAbstractState>>(), aborter);
    }

    /**
     * @param program The program to set.
     */
    public void clearAndSetNewProgram(PrologProgram program) {
        this.clearGraph();
        this.program = program;
        this.addNode(this.getRoot());
    }

    /**
     * @param query The query to set.
     */
    public void clearAndSetNewQuery(PrologQuery query) {
        this.clearGraph();
        final Triple<PrologTerm, Set<PrologAbstractVariable>, Set<PrologAbstractVariable>> triple =
            PrologEvaluationGraph.transformQuery(query, this.fridge);
        if (triple.x == null) { // no queries
            this.root =
                new Node<PrologAbstractState>(
                    PrologAbstractState.createEmptyState(this.getSMTFactory(), this.getSMTLogic())
                );
        } else {
            final Map<PrologAbstractVariable, PrologInterval> numbers =
                new LinkedHashMap<PrologAbstractVariable, PrologInterval>();
            for (PrologAbstractVariable v : triple.z) {
                numbers.put(v, new PrologInterval());
            }
            this.root =
                PrologEvaluationGraph.createCleanedNode(PrologAbstractState.createFromTerm(
                    triple.x,
                    KnowledgeBase.createWithGroundAndIntegers(
                        triple.y,
                        numbers,
                        this.getSMTFactory(),
                        this.getSMTLogic()
                    )
                )
            );
        }
        this.addNode(this.getRoot());
    }

    /**
     * @return The logic for SMT solvers.
     */
    public SMTLIBLogic getSMTLogic() {
        return this.smtLogic;
    }

    @Override
    public void clearGraph() {
        super.clearGraph();
        this.scope = 1;
        Set<String> used = this.getProgram().createSetOfAllSymbolNames();
        used.add("X");
        used.add("T");
        used.add("T0");
        this.fridge = new FreshNameGenerator(used, FreshNameGenerator.PROLOG_VARS);
        this.addNode(this.getRoot());
    }

    /**
     * Computes all results relevant for EVAL or ONLYEVAL operations.
     * @param stateElement The state element to expand.
     * @param kb The knowledge base to consider.
     * @param justOE Flag indicating whether one is just interested in the case that ONLYEVAL is applicable.
     * @param aborter For abortions.
     * @return All results relevant for EVAL or ONLYEVAL operations.
     */
    public EvalResults computeEvalResults(
        GoalElement stateElement,
        KnowledgeBase kb,
        boolean justOE,
        Abortion aborter
    ) {
        final PrologClause clause = this.getFreshlyRenamedClause(stateElement.getApplicableClause());
        final PrologTerm completeTerm = stateElement.getTerm();
        PrologTerm term = completeTerm;
        final PrologTerm head = clause.getHead();
        PrologTerm body = PrologEvaluationGraph.transformed(clause.getBody(), stateElement.getScope());
        final PrologClause toApply = new PrologClause(head, body);
        if (term.isConjunction()) {
            term = term.conjunctionHead();
        }
        // mgu(term, head) = sigma with V(Range(sigma)) \subseteq V_fresh
        final PrologSubstitution sigma = term.calculateMGUwithOnlyFreshVariables(head, this.getFNG());
        if (sigma == null) {
            return null;
        }
        // store check for BACKTRACK for initial sigma
        final boolean backtrack = PrologEvaluationGraph.checkForBacktrack(sigma);
        if (justOE && backtrack) {
            return null;
        }
        final PrologSubstitution sigmaG = sigma.restrict(kb.getGroundSet());
        final KnowledgeBase evalBase = kb.recordEvaluation(toApply, sigma, aborter);
        if (evalBase == null) {
            return null;
        }
        // body = b',q
        if (body == null) {
            if (completeTerm.isConjunction()) {
                body = completeTerm.conjunctionTail();
            } else {
                body = PrologTerms.createTrue();
            }
        } else {
            if (completeTerm.isConjunction()) {
                body = PrologTerms.createConjunction(body, completeTerm.conjunctionTail());
            }
        }
        final PrologSubstitution sigmaPrime;
        if (!kb.getGroundSet().containsAll(term.createSetOfAllAbstractVariables())) {
            sigmaPrime = sigma.append(this.refreshVarNames(body, sigma, evalBase, true));
        } else if (!kb.getFreeSet().containsAll(term.createSetOfAllNonAbstractVariables())) {
            sigmaPrime = sigma.append(this.refreshVarNames(body, sigma, evalBase, false));
        } else {
            sigmaPrime = sigma;
        }
        // body = (b',q)\sigma'
        body = body.applySubstitution(sigmaPrime);
        return new EvalResults(backtrack, body, evalBase, head, sigmaPrime, sigmaG, term, toApply);
    }

    /**
     * Error state, succeeding state and failure state are defined in Alexander Weinert's Master Thesis, in "Evaluation
     * of Integer Relations".
     * @param node Some node.
     * @param aborter For abortions.
     * @return A triple of error state, succeeding state, failure state in this order, if the head of the node is an
     *         arithmetic comparison. Null otherwise.
     */
    public Triple<Node<PrologAbstractState>, Node<PrologAbstractState>, Node<PrologAbstractState>> expandArithComp(
        Node<PrologAbstractState> node,
        Abortion aborter
    ) {
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final PrologAbstractState petToExpand = node.getObject();
        final GoalElement stateElementToExpand = petToExpand.getHeadOfState();
        if (stateElementToExpand.hasApplicableClause()) {
            return null;
        }
        PrologTerm termToExpand = stateElementToExpand.getTerm();
        if (termToExpand.isConjunction()) {
            termToExpand = termToExpand.conjunctionHead();
        }
        if (!PrologBuiltins.ARITHMETIC_COMPARISON_PREDICATES.contains(termToExpand.createFunctionSymbol())) {
            return null;
        }
        assert termToExpand.getArguments().size() == 2 : "Non-binary arithmetic comparison";
        final PrologTerm lhs = termToExpand.getArgument(0);
        final PrologTerm rhs = termToExpand.getArgument(1);
        final YNM lhsIsSafe = petToExpand.getKnowledgeBase().isSafe(lhs, aborter);
        final YNM rhsIsSafe = petToExpand.getKnowledgeBase().isSafe(rhs, aborter);
        final Node<PrologAbstractState> errorState;
        if (lhsIsSafe != YNM.YES || rhsIsSafe != YNM.YES) {
            errorState = new Node<>(PrologAbstractState.createErrorState(this.getSMTFactory(), this.getSMTLogic()));
            this.addEdge(node, errorState, new ArithCompErrorRule());
        } else {
            errorState = null;
        }
        final boolean truthValueOfRelation = petToExpand.getKnowledgeBase().checkArithComp(termToExpand, aborter);
        final boolean truthValueOfInverseRelation =
            petToExpand.getKnowledgeBase().checkArithCompInverse(termToExpand, aborter);
        final Node<PrologAbstractState> successNode;
        if (lhsIsSafe != YNM.NO && rhsIsSafe != YNM.NO && !truthValueOfInverseRelation) {
            // We have to account for the possibility that the relation evaluates to true, i.e., produce the success
            // state.
            final PrologTerm successTermHead;
            if (petToExpand.getHeadOfState().getTerm().isConjunction()) {
                successTermHead = petToExpand.getHeadOfState().getTerm().conjunctionTail();
            } else {
                successTermHead = PrologTerms.createTrue();
            }
            final GoalElement successHead =
                new GoalElement(successTermHead, petToExpand.getHeadOfState().getScope(), GoalElement.NO_CLAUSE);
            final List<GoalElement> successGoals = new LinkedList<>();
            successGoals.add(successHead);
            successGoals.addAll(petToExpand.getTailOfState());
            final KnowledgeBase successKnowledgeBase =
                petToExpand.getKnowledgeBase().assumeArithCompTrue(termToExpand, aborter);
            successNode = new Node<>(new PrologAbstractState(successGoals, successKnowledgeBase));
            this.addEdge(node, successNode, ArithCompCaseRule.createSuccessRule(termToExpand));
        } else {
            successNode = null;
        }
        final Node<PrologAbstractState> failureNode;
        if (lhsIsSafe != YNM.NO && rhsIsSafe != YNM.NO && !truthValueOfRelation) {
            // We have to account for the possibility that the relation evaluates to false, i.e., produce the failure
            // state.
            failureNode =
                new Node<PrologAbstractState>(
                    new PrologAbstractState(
                        petToExpand.getTailOfState(),
                        petToExpand.getKnowledgeBase().assumeArithCompFalse(termToExpand, aborter)
                    )
                );
            this.addEdge(node, failureNode, ArithCompCaseRule.createFailureRule(termToExpand));
        } else {
            failureNode = null;
        }
        return new Triple<>(errorState, successNode, failureNode);
    }

    public Node<PrologAbstractState> expandBacktrack(Node<PrologAbstractState> node) {
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final PrologAbstractState petToExpand = node.getObject();
        final GoalElement s = petToExpand.getHeadOfState();
        if (s == null || s.isQuestionMark() || !s.hasApplicableClause()) {
            return null;
        }
        final PrologTerm completeTerm = s.getTerm();
        PrologTerm t = completeTerm;
        if (t.isConjunction()) {
            t = t.conjunctionHead();
        }
        final KnowledgeBase kb = petToExpand.getKnowledgeBase();
        final PrologClause clause = this.getProgram().getClause(s.getApplicableClause());
        final PrologTerm h = clause.getHead().nonAbstractVarsRefreshed(this.getFNG());
        final PrologSubstitution sigma = h.calculateMGUwithOnlyFreshVariables(t, this.getFNG());
        final Pair<PrologTerm, PrologTerm> clash;
        if (sigma == null) {
            clash = null;
        } else {
            clash = kb.computePossibleClash(sigma);
            if (clash == null) {
                return null;
            }
        }
        final Node<PrologAbstractState> res =
            PrologEvaluationGraph.createCleanedNode(new PrologAbstractState(petToExpand.getTailOfState(), kb));
        this.addEdge(node, res, new BacktrackRule(clause, clash));
        return res;
    }

    /**
     * Expands the given node using the CALL rule if possible. To indicate
     * failure it returns null. Otherwise it returns the child node of the
     * given node after the expansion.
     * @param node The node to expand using the CALL rule.
     * @return The child node after expansion or null if expansion fails.
     */
    public Node<PrologAbstractState> expandCall(Node<PrologAbstractState> node) {
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final PrologAbstractState petToExpand = node.getObject();
        final GoalElement s = petToExpand.getHeadOfState();
        if (s == null || s.isQuestionMark() || s.hasApplicableClause()) {
            return null;
        }
        PrologTerm t = s.getTerm();
        final PrologTerm completeTerm = s.getTerm();
        if (t.isConjunction()) {
            t = t.conjunctionHead();
        }
        if (!t.isCall()) {
            return null;
        }
        final List<GoalElement> newState = new ArrayList<GoalElement>();
        PrologTerm newTerm = PrologEvaluationGraph.transformed(t.getArgument(0), this.scope);
        if (completeTerm.isConjunction()) {
            newTerm = PrologTerms.createConjunction(newTerm, completeTerm.conjunctionTail());
        }
        newState.add(new GoalElement(newTerm));
        newState.add(new GoalElement(this.scope));
        newState.addAll(petToExpand.getTailOfState());
        this.scope++;
        final Node<PrologAbstractState> res =
            PrologEvaluationGraph.createCleanedNode(new PrologAbstractState(newState, petToExpand.getKnowledgeBase()));
        this.addEdge(node, res, new CallRule());
        return res;
    }

    /**
     * Expands the given node using the CASE rule if possible. To
     * indicate failure it returns null. Otherwise it returns the
     * child node of the given node after the expansion.
     * @param node The node to expand using the CASE rule.
     * @return The child node after expansion or null if expansion
     *         fails.
     */
    public Node<PrologAbstractState> expandCase(Node<PrologAbstractState> node) {
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final PrologAbstractState petToExpand = node.getObject();
        final GoalElement s = petToExpand.getHeadOfState();
        if (s == null || s.isQuestionMark() || s.hasApplicableClause()) {
            return null;
        }
        PrologTerm t = s.getTerm();
        if (t.isConjunction()) {
            t = t.conjunctionHead();
        }
        if (PrologBuiltins.BUILTIN_PREDICATES.contains(t.createFunctionSymbol())) {
            return null;
        }
        final List<Integer> slice = this.slice(t);
        if (slice.isEmpty() /*&& !this.emptyProgram*/) {
            //            throw new UndefinedCallException();
            return null;
        }
        final List<GoalElement> newState = new ArrayList<GoalElement>();
        for (Integer i : slice) {
            newState.add(new GoalElement(s.getTerm(), this.scope, i));
        }
        newState.add(new GoalElement(this.scope));
        this.scope++;
        newState.addAll(petToExpand.getTailOfState());
        final Node<PrologAbstractState> res =
            PrologEvaluationGraph.createCleanedNode(new PrologAbstractState(newState, petToExpand.getKnowledgeBase()));
        this.addEdge(node, res, new CaseRule());
        //        this.addEdge(node, res, new CaseRule(slice.isEmpty()));
        return res;
    }

    public Node<PrologAbstractState> expandCut(Node<PrologAbstractState> node) {
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final PrologAbstractState petToExpand = node.getObject();
        final GoalElement s = petToExpand.getHeadOfState();
        if (s == null || s.isQuestionMark() || s.hasApplicableClause()) {
            return null;
        }
        final PrologTerm completeTerm = s.getTerm();
        PrologTerm t = completeTerm;
        if (completeTerm.isConjunction()) {
            t = completeTerm.conjunctionHead();
        }
        if (!t.isCut()) {
            return null;
        }
        final List<GoalElement> newState = new ArrayList<GoalElement>();
        PrologTerm newTerm;
        if (completeTerm.isConjunction()) {
            newTerm = completeTerm.conjunctionTail();
        } else {
            newTerm = PrologTerms.createTrue();
        }
        newState.add(new GoalElement(newTerm));
        if (t instanceof LabeledCut) {
            final LabeledCut cut = (LabeledCut) t;
            final int number = cut.getNumber();
            boolean found = false;
            for (GoalElement elem : petToExpand.getTailOfState()) {
                if (found) {
                    newState.add(elem);
                } else if (elem.isQuestionMark() && elem.getScope() == number) {
                    found = true;
                }
            }
        }
        final Node<PrologAbstractState> res =
            PrologEvaluationGraph.createCleanedNode(new PrologAbstractState(newState, petToExpand.getKnowledgeBase()));
        this.addEdge(node, res, new CutRule());
        return res;
    }

    /**
     * @param node
     * @param aborter For abortions.
     */
    public Pair<Node<PrologAbstractState>, Node<PrologAbstractState>> expandEval(
        Node<PrologAbstractState> node,
        Abortion aborter
    ) {
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final PrologAbstractState petToExpand = node.getObject();
        final GoalElement stateElement = petToExpand.getHeadOfState();
        if (stateElement == null || stateElement.isQuestionMark() || !stateElement.hasApplicableClause()) {
            return null;
        }
        final KnowledgeBase kb = petToExpand.getKnowledgeBase();
        final EvalResults res = this.computeEvalResults(stateElement, kb, false, aborter);
        if (res == null) {
            return null;
        }
        final List<GoalElement> state = new ArrayList<GoalElement>();
        // add (b',q)\sigma'
        state.add(new GoalElement(res.getBody()));
        // apply sigmaG on S
        for (GoalElement element : petToExpand.getTailOfState()) {
            state.add(element.applySubstitution(res.getSigmaG()));
        }
        final Node<PrologAbstractState> evalNode =
            PrologEvaluationGraph.createCleanedNode(new PrologAbstractState(state, res.getEvalBase()));
        if (res.canBacktrack()) {
            final KnowledgeBase backtrackBase =
                kb.setNonUnify(res.getTerm(), res.getHead()).addFreeVariables(
                    res.getHead().createSetOfAllNonAbstractVariables());
            final Node<PrologAbstractState> backtrackNode =
                PrologEvaluationGraph.createCleanedNode(new PrologAbstractState(petToExpand.getTailOfState(), backtrackBase));
            this.addEdge(node, evalNode, new EvalRule(res.getToApply(), res.getSigma(), res.getSigmaG()));
            this.addEdge(
                node,
                backtrackNode,
                new EvalRule(new Pair<PrologTerm, PrologTerm>(res.getTerm(), res.getHead())));
            return new Pair<Node<PrologAbstractState>, Node<PrologAbstractState>>(evalNode, backtrackNode);
        } else {
            this.addEdge(node, evalNode, new OnlyEvalRule(res.getToApply(), res.getSigma(), res.getSigmaG()));
            return new Pair<Node<PrologAbstractState>, Node<PrologAbstractState>>(evalNode, null);
        }
    }

    public Node<PrologAbstractState> expandFailure(Node<PrologAbstractState> node) {
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final PrologAbstractState petToExpand = node.getObject();
        final GoalElement s = petToExpand.getHeadOfState();
        if (s == null) {
            return null;
        } else if (!s.isQuestionMark()) {
            PrologTerm t = s.getTerm();
            if (t.isConjunction()) {
                t = t.conjunctionHead();
            }
            if (!t.isFail()) {
                return null;
            }
        }
        final Node<PrologAbstractState> res =
            PrologEvaluationGraph.createCleanedNode(
                new PrologAbstractState(petToExpand.getTailOfState(), petToExpand.getKnowledgeBase())
            );
        this.addEdge(node, res, new FailureRule());
        return res;
    }

    /**
     * @param node
     * @param aborter For abortions.
     * @return
     */
    public boolean expandGeneralization(
        Node<PrologAbstractState> node,
        Node<PrologAbstractState> generalizedNode,
        GeneralizationRule rule,
        boolean noGroundLoss,
        Abortion aborter
    ) {
        //        Node<AbstractState> node, Map<Integer,Map<Occurence,PrologAbstractVariable>> generalization, KnowledgeBase newGround) {
        if (
            !this.contains(node)
            || !this.getOut(node).isEmpty()
            || node.getObject().getState().size() != 1
            || !PrologAbstractState.checkInstanceMatcher(
                    node.getObject(),
                    generalizedNode.getObject(),
                    rule.getGeneralizationAsSubstitution(),
                    noGroundLoss,
                    aborter
                )
        ) {
            return false;
        }
        //        AbstractState newAbstractState = node.getObject().deepCopy();
        //        List<StateElement> state = newAbstractState.getState();
        //        int size = state.size();
        //        PrologSubstitution generalizationSubstitution = new PrologSubstitution();
        //        newAbstractState.getKnowledgeBase().addInfos(newGround);
        //        for (Map.Entry<Integer, Map<Occurence,PrologAbstractVariable>> entry : generalization.entrySet()) {
        //            int positionOfStateElement = entry.getKey();
        //            if (positionOfStateElement >= size) {
        //                return null;
        //            }
        //            StateElement element = state.get(positionOfStateElement);
        //            if (element.isQuestionMark()) {
        //                return null;
        //            }
        //            PrologTerm term = element.getTerm();
        //            for (Map.Entry<Occurence, PrologAbstractVariable> replacement : entry.getValue().entrySet()) {
        //                Occurence occ = replacement.getKey();
        //                PrologAbstractVariable var = replacement.getValue();
        //                PrologTerm replaced = term.getSubterm(occ);
        //                if (replaced == null) {
        //                    return null;
        //                }
        //                term.setSubterm(var, occ);
        //                generalizationSubstitution.put(var, replaced);
        //            }
        //        }
        this.addEdge(node, generalizedNode, rule);
        return true;
    }

    /**
     * @param node
     * @return
     */
    public Node<PrologAbstractState> expandGeneralizationInGraph(
        Node<PrologAbstractState> node,
        int maxNestedDepth,
        boolean generalizeAtFirstOccurence
    ) {
        if (!this.contains(node) || !this.getOut(node).isEmpty() || maxNestedDepth < 1) {
            return null;
        }
        final PrologAbstractState petToExpand = node.getObject();
        if (petToExpand.getState().size() != 1) {
            return null;
        }
        final GoalElement s = petToExpand.getHeadOfState();
        if (s == null || s.isQuestionMark() || s.hasApplicableClause()) {
            return null;
        }
        final PrologTerm t = s.getTerm();
        final Set<Occurrence> generalizationPositions =
            PrologEvaluationGraph.calculateGeneralizationPositions(t, maxNestedDepth, generalizeAtFirstOccurence);
        if (generalizationPositions.isEmpty()) {
            return null;
        } else {
            PrologTerm newTerm = t;
            final KnowledgeBase base = petToExpand.getKnowledgeBase();
            final Set<PrologAbstractVariable> ground = new LinkedHashSet<PrologAbstractVariable>();
            final PrologSubstitution generalizations = new PrologSubstitution();
            for (Occurrence occ : generalizationPositions) {
                final PrologAbstractVariable v = this.getFreshAbstractVariable();
                final PrologTerm subterm = t.getSubterm(occ);
                if (base.isGround(subterm)) {
                    ground.add(v);
                }
                generalizations.put(v, subterm);
                newTerm = newTerm.replace(v, occ);
            }
            final Node<PrologAbstractState> res =
                PrologEvaluationGraph.createCleanedNode(
                    PrologAbstractState.createFromTerm(newTerm, base.addGroundVariables(ground))
                );
            this.addEdge(
                node,
                res,
                new GeneralizationRule(
                    generalizations,
                    KnowledgeBase.createWithGroundVars(ground, this.getSMTFactory(), this.getSMTLogic())
                )
            );
            return res;
        }
    }

    /**
     * @param node
     * @param aborter For abortions.
     * @return
     */
    public Node<PrologAbstractState> expandInstance(
        Node<PrologAbstractState> node,
        Iterable<Node<PrologAbstractState>> iterator,
        boolean noGroundLoss,
        Abortion aborter
    ) {
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final PrologAbstractState petToExpand = node.getObject();
        if (petToExpand.getState().size() != 1) {
            // instances with more than 1 element need more complicated rules/clauses
            return null;
        }
        for (Node<PrologAbstractState> toCheck : iterator) {
            if (!this.contains(toCheck)) {
                continue;
            }
            final PrologSubstitution matcher =
                PrologAbstractState.calculateInstanceMatcher(petToExpand, toCheck.getObject(), noGroundLoss, aborter);
            if (matcher != null) {
                this.addEdge(node, toCheck, new InstanceRule(matcher));
                return toCheck;
            }
        }
        return null;
    }

    public Triple<Node<PrologAbstractState>, Node<PrologAbstractState>, Node<PrologAbstractState>> expandIs(
        Node<PrologAbstractState> node,
        Abortion aborter
    ) {
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final PrologAbstractState petToExpand = node.getObject();
        final GoalElement stateElementToExpand = petToExpand.getHeadOfState();
        if (stateElementToExpand == null || stateElementToExpand.isQuestionMark() || stateElementToExpand.hasApplicableClause()) {
            return null;
        }
        PrologTerm termToExpand = stateElementToExpand.getTerm();
        if (termToExpand.isConjunction()) {
            termToExpand = termToExpand.conjunctionHead();
        }
        if (!PrologBuiltin.IS_PREDICATE.equals(termToExpand.createFunctionSymbol())) {
            return null;
        }
        assert termToExpand.getArguments().size() == 2 : "Is-predicate without two arguments";
        final PrologTerm target = termToExpand.getArgument(0);
        final PrologTerm expr = termToExpand.getArgument(1);
        final YNM exprEvaluationIsSafe = petToExpand.getKnowledgeBase().isSafe(expr, aborter);
        final Node<PrologAbstractState> errorState;
        if (exprEvaluationIsSafe != YNM.YES) {
            errorState = new Node<>(PrologAbstractState.createErrorState(this.getSMTFactory(), this.getSMTLogic()));
            this.addEdge(node, errorState, new IsErrorRule());
        } else {
            errorState = null;
        }
        final Node<PrologAbstractState> successState, failureState;
        if (exprEvaluationIsSafe == YNM.NO) {
            successState = null;
            failureState = null;
        } else if (target.isCompound() || target.isAtom(this.program.createSetOfAllPredicates())) {
            // Build success state
            successState = null;
            // Build failure state
            final List<GoalElement> failureStateElements = petToExpand.getTailOfState();
            final KnowledgeBase failureKb = petToExpand.getKnowledgeBase().assumeUnificationFail(target, expr);
            failureState = new Node<>(new PrologAbstractState(failureStateElements, failureKb));
            this.addEdge(node, failureState, new IsErrorRule());
        } else if (target.isNumber()) {
            final PrologTerm arithCompTerm = PrologTerm.create(PrologBuiltin.ISEQUAL_NAME, target, expr);
            final boolean truthValueOfTerm = petToExpand.getKnowledgeBase().checkArithComp(arithCompTerm, aborter);
            final boolean truthValueOfInverseTerm =
                petToExpand.getKnowledgeBase().checkArithCompInverse(arithCompTerm, aborter);
            // Build success state TODO check inverse relations!
            if (!truthValueOfInverseTerm) {
                final PrologTerm successTerms;
                if (petToExpand.getHeadOfState().getTerm().isConjunction()){
                    successTerms = petToExpand.getHeadOfState().getTerm().conjunctionTail();
                } else {
                    successTerms = PrologTerms.createTrue();
                }
                final KnowledgeBase successKnowledgeBase =
                    petToExpand.getKnowledgeBase().assumeArithCompTrue(arithCompTerm, aborter);
                final List<GoalElement> successStateElements = new LinkedList<>();
                successStateElements.add(
                    new GoalElement(successTerms, stateElementToExpand.getScope(), GoalElement.NO_CLAUSE)
                );
                successStateElements.addAll(petToExpand.getTailOfState());
                successState = new Node<>(new PrologAbstractState(successStateElements, successKnowledgeBase));
                this.addEdge(
                    node,
                    successState,
                    new IsSuccessRule(new PrologSubstitution(), new Pair<PrologTerm, PrologTerm>(target, expr))
                );
            } else {
                successState = null;
            }
            // Build failure state
            if (!truthValueOfTerm) {
                failureState =
                    new Node<PrologAbstractState>(
                        new PrologAbstractState(
                            petToExpand.getTailOfState(),
                            petToExpand.getKnowledgeBase().assumeArithCompFalse(arithCompTerm, aborter)
                        )
                    );
                this.addEdge(node, failureState, new IsFailRule(new Pair<PrologTerm, PrologTerm>(target, expr)));
            } else {
                failureState = null;
            }
        } else if (target.isNonAbstractVariable()) {
            // Build success state
            final PrologAbstractVariable freshVariable = this.getFreshAbstractVariable();
            final Map<PrologNonAbstractVariable, PrologAbstractVariable> substitution =
                Collections.singletonMap((PrologNonAbstractVariable)target, freshVariable);
            final PrologTerm successTerms =
                petToExpand.getHeadOfState().getTerm().isConjunction() ?
                    petToExpand.getHeadOfState().getTerm().conjunctionTail() :
                        PrologTerms.createTrue();
            final PrologTerm renamedSuccessTerms = successTerms.applySubstitution(substitution);
            final PrologTerm arithCompTerm = PrologTerm.create(PrologBuiltin.ISEQUAL_NAME, freshVariable, expr);
            final KnowledgeBase successKnowledgeBase =
                petToExpand.getKnowledgeBase().assumeArithCompTrue(arithCompTerm, aborter);
            final List<GoalElement> successStateElements = new LinkedList<>();
            successStateElements.add(
                new GoalElement(renamedSuccessTerms, stateElementToExpand.getScope(), GoalElement.NO_CLAUSE)
            );
            for (GoalElement oldStateElement : petToExpand.getTailOfState()) {
                successStateElements.add(oldStateElement.applySubstitution(substitution));
            }
            successState = new Node<>(new PrologAbstractState(successStateElements, successKnowledgeBase));
            this.addEdge(
                node,
                successState,
                new IsSuccessRule(new PrologSubstitution(substitution), new Pair<PrologTerm, PrologTerm>(target, expr))
            );
            failureState = null;
        } else if (target.isAbstractVariable()) {
            // Build success state
            final PrologAbstractVariable freshVariable = this.getFreshAbstractVariable();
            final Map<PrologAbstractVariable, PrologAbstractVariable> substitution =
                Collections.singletonMap((PrologAbstractVariable)target, freshVariable);
            final PrologTerm successTerms =
                petToExpand.getHeadOfState().getTerm().isConjunction() ?
                    petToExpand.getHeadOfState().getTerm().conjunctionTail() :
                        PrologTerms.createTrue();
            final PrologTerm renamedSuccessTerms = successTerms.applySubstitution(substitution);
            final PrologTerm arithCompTerm = PrologTerm.create(PrologBuiltin.ISEQUAL_NAME, freshVariable, expr);
            final KnowledgeBase successKnowledgeBase =
                petToExpand.getKnowledgeBase().assumeArithCompTrue(arithCompTerm, aborter);
            final List<GoalElement> successStateElements = new LinkedList<>();
            successStateElements.add(
                new GoalElement(renamedSuccessTerms, stateElementToExpand.getScope(), GoalElement.NO_CLAUSE)
            );
            for (GoalElement oldStateElement : petToExpand.getTailOfState()) {
                successStateElements.add(oldStateElement.applySubstitution(substitution));
            }
            successState = new Node<>(new PrologAbstractState(successStateElements, successKnowledgeBase));
            this.addEdge(
                node,
                successState,
                new IsSuccessRule(new PrologSubstitution(substitution), new Pair<PrologTerm, PrologTerm>(target, expr))
            );
            // Build failure state
            failureState =
                new Node<PrologAbstractState>(
                    new PrologAbstractState(
                        petToExpand.getTailOfState(),
                        petToExpand.getKnowledgeBase().assumeSafeEvaluation(expr)
                    )
                );
            this.addEdge(node, failureState, new IsFailRule(new Pair<PrologTerm, PrologTerm>(target, expr)));
        } else {
            throw new IllegalStateException("Should never get here");
        }
        return new Triple<>(errorState, successState, failureState);
    }

    public Node<PrologAbstractState> expandNot(Node<PrologAbstractState> node) {
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final PrologAbstractState petToExpand = node.getObject();
        final GoalElement s = petToExpand.getHeadOfState();
        if (s == null || s.isQuestionMark() || s.hasApplicableClause()) {
            return null;
        }
        PrologTerm t = s.getTerm();
        final PrologTerm completeTerm = s.getTerm();
        if (t.isConjunction()) {
            t = t.conjunctionHead();
        }
        if (!PrologBuiltin.NOT_PREDICATE.equals(t.createFunctionSymbol())) {
            return null;
        }
        final List<GoalElement> newState = new ArrayList<GoalElement>();
        final List<PrologTerm> conjuncts = new ArrayList<PrologTerm>();
        conjuncts.add(PrologTerms.createCall(t.getArgument(0)));
        conjuncts.add(new LabeledCut(this.scope));
        conjuncts.add(PrologTerms.createFail());
        final PrologTerm newTerm = PrologTerms.createConjunction(conjuncts);
        PrologTerm tailTerm = PrologTerms.createTrue();
        if (completeTerm.isConjunction()) {
            tailTerm = completeTerm.conjunctionTail();
        }
        newState.add(new GoalElement(newTerm));
        newState.add(new GoalElement(tailTerm));
        newState.add(new GoalElement(this.scope));
        newState.addAll(petToExpand.getTailOfState());
        this.scope++;
        final Node<PrologAbstractState> res =
            PrologEvaluationGraph.createCleanedNode(new PrologAbstractState(newState, petToExpand.getKnowledgeBase()));
        this.addEdge(node, res, new NotRule());
        return res;
    }

    public Pair<Node<PrologAbstractState>, Node<PrologAbstractState>> expandParallel(
        Node<PrologAbstractState> node,
        int numberOfStateElements
    ) {
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final PrologAbstractState petToExpand = node.getObject();
        final List<GoalElement> state = petToExpand.getState();
        if (numberOfStateElements >= state.size() || numberOfStateElements < 1) {
            return null;
        }
        final List<GoalElement> s1 = new ArrayList<GoalElement>();
        final List<GoalElement> s2 = new ArrayList<GoalElement>();
        for (int i = 0; i < numberOfStateElements; i++) {
            s1.add(state.get(i));
        }
        final Set<Integer> ac = this.calculateActiveCuts(s1);
        for (int i = numberOfStateElements; i < state.size(); i++) {
            final GoalElement e = state.get(i);
            if (i > numberOfStateElements && i < state.size() - 1 && e.isQuestionMark() && ac.contains(e.getScope())) {
                return null;
            }
            s2.add(e);
        }
        final KnowledgeBase kb = petToExpand.getKnowledgeBase();
        final Node<PrologAbstractState> node1 = PrologEvaluationGraph.createCleanedNode(new PrologAbstractState(s1, kb));
        final Node<PrologAbstractState> node2 = PrologEvaluationGraph.createCleanedNode(new PrologAbstractState(s2, kb));
        this.addEdge(node, node1, new ParallelRule(true));
        this.addEdge(node, node2, new ParallelRule(false));
        return new Pair<Node<PrologAbstractState>, Node<PrologAbstractState>>(node1, node2);
    }

    /**
     * @param node
     */
    public Pair<Node<PrologAbstractState>, Node<PrologAbstractState>> expandSplit(
        Node<PrologAbstractState> node,
        GroundnessAnalysis analysis
    ) {
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final PrologAbstractState petToExpand = node.getObject();
        final List<GoalElement> state = petToExpand.getState();
        if (state.size() != 1) {
            return null;
        }
        final GoalElement s = state.get(0);
        if (s.isQuestionMark() || s.hasApplicableClause()) {
            return null;
        }
        final PrologTerm completeTerm = s.getTerm();
        if (!completeTerm.isConjunction()) {
            return null;
        }
        final KnowledgeBase kb = petToExpand.getKnowledgeBase();
        final PrologTerm t = completeTerm.conjunctionHead();
        PrologTerm q = completeTerm.conjunctionTail();
        final Set<PrologNonAbstractVariable> freeT = new LinkedHashSet<PrologNonAbstractVariable>();
        boolean moreReplacements = false;
        // calculate the set F(t) and check whether
        // \mu has to replace more variables than this
        for (PrologVariable v : t.createSetOfAllVariables()) {
            if (v.isNonAbstractVariable()) {
                final PrologNonAbstractVariable n = (PrologNonAbstractVariable)v;
                if (kb.isFree(n)) {
                    freeT.add(n);
                } else {
                    moreReplacements = true;
                }
            } else if (!moreReplacements && v.isAbstractVariable()) {
                if (!kb.isGround(v)) {
                    moreReplacements = true;
                }
            }
        }
        // F' = F \ F(t)
        final Set<PrologNonAbstractVariable> qFree = new LinkedHashSet<PrologNonAbstractVariable>(kb.getFreeSet());
        qFree.removeAll(freeT);
        // calculate \mu
        final PrologSubstitution mu = new PrologSubstitution();
        for (PrologVariable v : freeT) {
            mu.put(v, this.getFreshAbstractVariable());
        }
        if (moreReplacements) {
            final Set<PrologVariable> toReplace = q.createSetOfAllVariables();
            toReplace.addAll(kb.getAllVars());
            toReplace.removeAll(kb.getGroundSet());
            toReplace.removeAll(kb.getFreeSet());
            for (PrologVariable v : toReplace) {
                mu.put(v, this.getFreshAbstractVariable());
            }
        }
        // q\mu in second split child
        q = q.applySubstitution(mu);
        // U\mu in knowledge base for q
        final Set<Pair<PrologTerm, PrologTerm>> qNonunify = new LinkedHashSet<Pair<PrologTerm, PrologTerm>>();
        for (Pair<PrologTerm, PrologTerm> pair : kb.getNonUnifyingTerms()) {
            qNonunify.add(new Pair<PrologTerm, PrologTerm>(pair.x.applySubstitution(mu), pair.y.applySubstitution(mu)));
        }
        // calculate G'
        final Set<Integer> groundPositions = new LinkedHashSet<Integer>();
        for (int i = 0; i < t.getArity(); i++) {
            if (kb.isGround(t.getArgument(i))) {
                groundPositions.add(i);
            }
        }
        //        KnowledgeBase newKnowledge = new KnowledgeBase();
        final Set<PrologAbstractVariable> qGround = new LinkedHashSet<PrologAbstractVariable>(kb.getGroundSet());
        final Set<PrologAbstractVariable> newGround = new LinkedHashSet<PrologAbstractVariable>();
        for (Integer i : analysis.getGroundPositions(t.createFunctionSymbol(), groundPositions)) {
            final PrologTerm child = t.getArgument(i).applySubstitution(mu);
            final Set<PrologAbstractVariable> ground = child.createSetOfAllAbstractVariables();
            qGround.addAll(ground);
            newGround.addAll(ground);
        }
        // consider numbers TODO more precise handling? extend groundness analysis?
        final PrologSubstitution muI = mu.restrict(kb.getIntegerSet());
        final Map<PrologAbstractVariable, PrologInterval> qNumbers =
            new LinkedHashMap<PrologAbstractVariable, PrologInterval>(kb.getIntegerMap());
        for (Map.Entry<PrologVariable, PrologTerm> entry : muI.entrySet()) {
            final PrologVariable key = entry.getKey();
            final PrologTerm value = entry.getValue();
            if (value.isInt()) {
                if (!kb.getIntegerMap().get(key).contains((PrologInt) value)) {
                    return null;
                }
            } else if (value.isAbstractVariable()) {
                qNumbers.put((PrologAbstractVariable) value, kb.getIntegerMap().get(key));
            } else {
                return null;
            }
        }
        // create nodes and link them with edges
        final Node<PrologAbstractState> tNode =
            PrologEvaluationGraph.createCleanedNode(PrologAbstractState.createFromTerm(t, kb));
        final Node<PrologAbstractState> qNode =
            PrologEvaluationGraph.createCleanedNode(
                PrologAbstractState.createFromTerm(
                    q,
                    KnowledgeBase.create(
                        qGround,
                        qFree,
                        qNonunify,
                        qNumbers,
                        this.getSMTFactory(),
                        this.getSMTLogic()
                    )
                )
            );
        this.addEdge(node, tNode, new SplitRule(null));
        this.addEdge(
            node,
            qNode,
            new SplitRule(
                new SplitCase(
                    KnowledgeBase.createWithGroundVars(newGround, this.getSMTFactory(), this.getSMTLogic()),
                    mu
                )
            )
        );
        return new Pair<Node<PrologAbstractState>, Node<PrologAbstractState>>(tNode, qNode);
    }

    /**
     * Expands the given node using the SUCCESS rule if possible.
     * Returns null to indicate failure. Otherwise it returns the
     * child of the given node after the expansion.
     * @param node The node to expand using the SUCCESS rule.
     * @return The child of the node after expansion or null if
     *         expansion fails.
     */
    public Node<PrologAbstractState> expandSuccess(Node<PrologAbstractState> node) {
        final PrologAbstractState petToExpand = node.getObject();
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final GoalElement s = petToExpand.getHeadOfState();
        if (s == null || s.isQuestionMark() || s.hasApplicableClause()) {
            return null;
        }
        final PrologTerm t = s.getTerm();
        if (!t.isTrue()) {
            return null;
        }
        final Node<PrologAbstractState> res =
            PrologEvaluationGraph.createCleanedNode(
                new PrologAbstractState(petToExpand.getTailOfState(), petToExpand.getKnowledgeBase())
            );
        this.addEdge(node, res, new SuccessRule());
        return res;
    }

    public Node<PrologAbstractState> expandUndefinedError(Node<PrologAbstractState> node) {
        final PrologAbstractState petToExpand = node.getObject();
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final GoalElement s = petToExpand.getHeadOfState();
        if (s == null || s.isQuestionMark() || s.hasApplicableClause()) {
            return null;
        }
        PrologTerm t = s.getTerm();
        if (t.isConjunction()) {
            t = t.conjunctionHead();
        }
        if (PrologBuiltins.BUILTIN_PREDICATES.contains(t.createFunctionSymbol()) || t.isCut()) {
            return null;
        }
        if (!this.slice(t).isEmpty()) {
            return null;
        }
        final Node<PrologAbstractState> res =
            new Node<PrologAbstractState>(
                PrologAbstractState.createEmptyState(this.getSMTFactory(), this.getSMTLogic())
            );
        this.addEdge(node, res, new UndefinedErrorRule());
        return res;
    }

    public Pair<Node<PrologAbstractState>, Node<PrologAbstractState>> expandUnify(Node<PrologAbstractState> node) {
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final PrologAbstractState petToExpand = node.getObject();
        final GoalElement s = petToExpand.getHeadOfState();
        if (s == null || s.isQuestionMark() || s.hasApplicableClause()) {
            return null;
        }
        PrologTerm t = s.getTerm();
        final PrologTerm completeTerm = s.getTerm();
        if (t.isConjunction()) {
            t = t.conjunctionHead();
        }
        if (!PrologBuiltin.UNIFY_PREDICATE.equals(t.createFunctionSymbol())) {
            return null;
        }
        final KnowledgeBase kb = petToExpand.getKnowledgeBase();
        final PrologTerm t1 = t.getArgument(0);
        final PrologTerm t2 = t.getArgument(1);
        final PrologSubstitution sigma = t1.calculateMGUwithOnlyFreshVariables(t2, this.getFNG());
        if (sigma == null) {
            return null;
        }
        // check for BACKTRACK
        final boolean backtrack = PrologEvaluationGraph.checkForBacktrack(sigma);
        final PrologSubstitution sigmaG = sigma.restrict(kb.getGroundSet());
        // G' = G \cup A(Range(sigma|_G))
        final Set<PrologAbstractVariable> ground = new LinkedHashSet<PrologAbstractVariable>(kb.getGroundSet());
        ground.addAll(sigmaG.getAbstractVarsInRange());
        // exclusion = F
        final Set<PrologNonAbstractVariable> exclusion = new LinkedHashSet<PrologNonAbstractVariable>(kb.getFreeSet());
        // fRange = N(Range(sigma|_F))
        final Set<PrologNonAbstractVariable> fRange = sigma.restrict(kb.getFreeSet()).getNonAbstractVarsInRange();
        // fRange = N(Range(sigma|_F)) \ N(Range(sigma|_{N \ F})))
        fRange.removeAll(sigma
            .restrictToNonAbstractVariables()
            .restrictExclusion(exclusion)
            .getNonAbstractVarsInRange());
        // F' = F \cup fRange
        final Set<PrologNonAbstractVariable> free = new LinkedHashSet<PrologNonAbstractVariable>(kb.getFreeSet());
        free.addAll(fRange);
        // U\sigma|_G in evalBase
        final Set<Pair<PrologTerm, PrologTerm>> nonunify = new LinkedHashSet<Pair<PrologTerm, PrologTerm>>();
        for (Pair<PrologTerm, PrologTerm> pair : kb.getNonUnifyingTerms()) {
            nonunify.add(new Pair<PrologTerm, PrologTerm>(pair.x.applySubstitution(sigmaG), pair.y
                .applySubstitution(sigmaG)));
        }
        // numbers is the map of the new integers TODO more precise documentation
        final PrologSubstitution sigmaI = sigma.restrict(kb.getIntegerSet());
        final Map<PrologAbstractVariable, PrologInterval> numbers =
            new LinkedHashMap<PrologAbstractVariable, PrologInterval>(kb.getIntegerMap());
        for (Map.Entry<PrologVariable, PrologTerm> entry : sigmaI.entrySet()) {
            final PrologVariable key = entry.getKey();
            final PrologTerm value = entry.getValue();
            if (value.isInt()) {
                if (!kb.getIntegerMap().get(key).contains((PrologInt) value)) {
                    return null;
                }
            } else if (value.isAbstractVariable()) {
                numbers.put((PrologAbstractVariable) value, kb.getIntegerMap().get(key));
            } else {
                return null;
            }
        }
        final KnowledgeBase evalBase =
            KnowledgeBase.create(ground, free, nonunify, numbers, this.getSMTFactory(), this.getSMTLogic());
        final PrologTerm q = (completeTerm.isConjunction() ? completeTerm.conjunctionTail() : PrologTerms.createTrue());
        final PrologSubstitution sigmaPrime;
        if (!kb.getGroundSet().containsAll(t.createSetOfAllAbstractVariables())) {
            sigmaPrime = sigma.append(this.refreshVarNames(q, sigma, evalBase, true));
        } else if (!kb.getFreeSet().containsAll(t.createSetOfAllNonAbstractVariables())) {
            sigmaPrime = sigma.append(this.refreshVarNames(q, sigma, evalBase, false));
        } else {
            sigmaPrime = sigma;
        }
        final List<GoalElement> state = new ArrayList<GoalElement>();
        state.add(new GoalElement(q.applySubstitution(sigmaPrime)));
        // apply sigmaG on S
        for (GoalElement element : petToExpand.getTailOfState()) {
            state.add(element.applySubstitution(sigmaG));
        }
        final Node<PrologAbstractState> evalNode =
            PrologEvaluationGraph.createCleanedNode(new PrologAbstractState(state, evalBase));
        if (backtrack) {
            final KnowledgeBase backtrackBase = kb.setNonUnify(t1, t2);
            final Node<PrologAbstractState> backtrackNode =
                PrologEvaluationGraph.createCleanedNode(new PrologAbstractState(petToExpand.getTailOfState(), backtrackBase));
            this.addEdge(node, evalNode, new UnifyCaseRule(sigmaPrime, sigmaG));
            this.addEdge(node, backtrackNode, new UnifyCaseRule(new Pair<PrologTerm, PrologTerm>(t1, t2)));
            return new Pair<Node<PrologAbstractState>, Node<PrologAbstractState>>(evalNode, backtrackNode);
        } else {
            this.addEdge(node, evalNode, new UnifySuccessRule(sigmaPrime, sigmaG));
            return new Pair<Node<PrologAbstractState>, Node<PrologAbstractState>>(evalNode, null);
        }
    }

    public Node<PrologAbstractState> expandUnifyFail(Node<PrologAbstractState> node) {
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final PrologAbstractState petToExpand = node.getObject();
        final GoalElement s = petToExpand.getHeadOfState();
        if (s == null || s.isQuestionMark() || s.hasApplicableClause()) {
            return null;
        }
        PrologTerm t = s.getTerm();
        if (t.isConjunction()) {
            t = t.conjunctionHead();
        }
        if (!PrologBuiltin.UNIFY_PREDICATE.equals(t.createFunctionSymbol())) {
            return null;
        }
        final PrologTerm t1 = t.getArgument(0), t2 = t.getArgument(1);
        final PrologSubstitution sigma = t1.calculateMGUwithOnlyFreshVariables(t2, this.getFNG());
        final KnowledgeBase kb = petToExpand.getKnowledgeBase();
        Pair<PrologTerm, PrologTerm> clash = null;
        boolean found = false;
        if (sigma != null) {
            final PrologSubstitution sigmaG = sigma.restrict(kb.getGroundSet());
            outerLoop: for (Pair<PrologTerm, PrologTerm> pair : kb.getNonUnifyingTerms()) {
                final PrologTerm s1 = pair.x.applySubstitution(sigmaG);
                final PrologTerm s2 = pair.y.applySubstitution(sigmaG);
                final PrologSubstitution sigmaPrime = s1.calculateMGU(s2);
                if (sigmaPrime != null) {
                    for (Map.Entry<PrologVariable, PrologTerm> entry : sigmaPrime.entrySet()) {
                        if (entry.getKey().isAbstractVariable()) {
                            continue outerLoop;
                        }
                    }
                    found = true;
                    clash = pair;
                    break outerLoop;
                }
            }
            if (!found) {
                return null;
            }
        }
        final Node<PrologAbstractState> res =
            PrologEvaluationGraph.createCleanedNode(new PrologAbstractState(petToExpand.getTailOfState(), kb));
        this.addEdge(node, res, new UnifyFailRule(clash));
        return res;
    }

    public Node<PrologAbstractState> expandVariableError(Node<PrologAbstractState> node) {
        final PrologAbstractState petToExpand = node.getObject();
        if (!this.contains(node) || !this.getOut(node).isEmpty()) {
            return null;
        }
        final GoalElement s = petToExpand.getHeadOfState();
        if (s == null || s.isQuestionMark() || s.hasApplicableClause()) {
            return null;
        }
        PrologTerm t = s.getTerm();
        if (t.isConjunction()) {
            t = t.conjunctionHead();
        }
        if (!t.isCall() && !t.isNonAbstractVariable()) {
            return null;
        }
        if (t.isCall()) {
            t = t.getArgument(0);
        }
        if (!t.isNonAbstractVariable()) {
            return null;
        }
        final Node<PrologAbstractState> res =
            new Node<PrologAbstractState>(
                PrologAbstractState.createEmptyState(this.getSMTFactory(), this.getSMTLogic())
            );
        this.addEdge(node, res, new VariableErrorRule());
        return res;
    }

    public Set<Node<PrologAbstractState>> getAncestors(Node<PrologAbstractState> n) {
        Node<PrologAbstractState> workNode = n;
        Set<Node<PrologAbstractState>> res = new LinkedHashSet<Node<PrologAbstractState>>();
        while (!workNode.equals(this.getRoot())) {
            workNode = this.getParent(workNode);
            res.add(workNode);
        }
        return res;
    }

    public Iterable<Node<PrologAbstractState>> getArithCompNodes() {
        Set<Node<PrologAbstractState>> res = new LinkedHashSet<Node<PrologAbstractState>>();
        for (Node<PrologAbstractState> node : this.getNodes()) {
            if (this.isArithCompNode(node)) {
                res.add(node);
            }
        }
        return res;
    }

    /**
     * Gathers all relevant nodes for the complexity transformation and returns them in a CpxNodeSets object.
     * @param aborter For abortions...
     * @return A CpxNodeSets object containing all relevant nodes for the complexity transformation.
     * @throws AbortionException If it is aborted...
     */
    public CpxNodeSets getCpxNodeSetsForPaths(Abortion aborter) throws AbortionException {
        Set<Node<PrologAbstractState>> instanceSet = new LinkedHashSet<Node<PrologAbstractState>>();
        Set<Node<PrologAbstractState>> parallelSet = new LinkedHashSet<Node<PrologAbstractState>>();
        Set<Node<PrologAbstractState>> splitSet = new LinkedHashSet<Node<PrologAbstractState>>();
        Set<Node<PrologAbstractState>> successSet = new LinkedHashSet<Node<PrologAbstractState>>();
        Set<Node<PrologAbstractState>> instanceChildren = new LinkedHashSet<Node<PrologAbstractState>>();
        for (Node<PrologAbstractState> node : this.getNodes()) {
            if (this.isInstanceNode(node) || this.isGeneralizationNode(node)) {
                instanceSet.add(node);
                instanceChildren.add(this.getFirstChild(node));
            } else if (this.isParallelNode(node)) {
                parallelSet.add(node);
            } else if (this.isSplitNode(node)) {
                splitSet.add(node);
            } else if (this.isSuccessNode(node)) {
                successSet.add(node);
            }
        }
        return new CpxNodeSets(instanceSet, successSet, parallelSet, splitSet, instanceChildren);
    }

    public Node<PrologAbstractState> getFirstChild(Node<PrologAbstractState> node) {
        Node<PrologAbstractState> res = null;
        for (Node<PrologAbstractState> n : this.getOut(node)) {
            res = n;
            break;
        }
        return res;
    }

    public Edge<AbstractInferenceRule, PrologAbstractState> getFirstSplitEdge(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (
                edge.getObject().rule() == AbstractInferenceRules.SPLIT
                && ((SplitRule) edge.getObject()).isFirstSplit()
            ) {
                return edge;
            }
        }
        return null;
    }

    public FreshNameGenerator getFNG() {
        return this.fridge;
    }

    public PrologAbstractVariable getFreshAbstractVariable() {
        return new PrologAbstractVariable(this.getFNG().getFreshName("T", false));
    }

    public PrologClause getFreshlyRenamedClause(int applicableClause) {
        return this.getProgram().getClause(applicableClause).nonAbstractVariablesRefreshed(this.getFNG());
    }

    public PrologNonAbstractVariable getFreshNonAbstractVariable() {
        return new PrologNonAbstractVariable(this.getFNG().getFreshName("X", false));
    }

    public Set<Node<PrologAbstractState>> getGeneralizationNodes() {
        Set<Node<PrologAbstractState>> res = new LinkedHashSet<Node<PrologAbstractState>>();
        for (Node<PrologAbstractState> node : this.getNodes()) {
            if (this.isGeneralizationNode(node)) {
                res.add(node);
            }
        }
        return res;
    }

    /**
     * @param node
     * @return
     */
    public Set<Node<PrologAbstractState>> getInstanceChildren(Node<PrologAbstractState> node) {
        Set<Node<PrologAbstractState>> res = new LinkedHashSet<Node<PrologAbstractState>>();
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getInEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.INSTANCE) {
                res.add(edge.getStartNode());
            }
        }
        return res;
    }

    public Set<Node<PrologAbstractState>> getInstanceNodes() {
        Set<Node<PrologAbstractState>> res = new LinkedHashSet<Node<PrologAbstractState>>();
        for (Node<PrologAbstractState> node : this.getNodes()) {
            if (this.isInstanceNode(node)) {
                res.add(node);
            }
        }
        return res;
    }

    public Iterable<Node<PrologAbstractState>> getIsNodes() {
        Set<Node<PrologAbstractState>> res = new LinkedHashSet<Node<PrologAbstractState>>();
        for (Node<PrologAbstractState> node : this.getNodes()) {
            if (this.isIsNode(node)) {
                res.add(node);
            }
        }
        return res;
    }

    public Node<PrologAbstractState> getLastChild(Node<PrologAbstractState> node) {
        Node<PrologAbstractState> res = null;
        for (Node<PrologAbstractState> n : this.getOut(node)) {
            res = n;
        }
        return res;
    }

    /**
     * Returns a triple of node-sets where the first set contains
     * all INSTANCE nodes, the second all SPLIT nodes and the third
     * all SUCCESS nodes.
     * @return A triple of special node-sets.
     */
    public NodeSets getNodeSetsForPaths() {
        Set<Node<PrologAbstractState>> instanceSet = new LinkedHashSet<Node<PrologAbstractState>>();
        Set<Node<PrologAbstractState>> generalizationSet = new LinkedHashSet<Node<PrologAbstractState>>();
        Set<Node<PrologAbstractState>> splitSet = new LinkedHashSet<Node<PrologAbstractState>>();
        Set<Node<PrologAbstractState>> successSet = new LinkedHashSet<Node<PrologAbstractState>>();
        Set<Node<PrologAbstractState>> instanceChildren = new LinkedHashSet<Node<PrologAbstractState>>();
        Set<Node<PrologAbstractState>> generalizationChildren = new LinkedHashSet<Node<PrologAbstractState>>();
        for (Node<PrologAbstractState> node : this.getNodes()) {
            if (this.isInstanceNode(node)) {
                instanceSet.add(node);
                instanceChildren.add(this.getFirstChild(node));
            } else if (this.isGeneralizationNode(node)) {
                generalizationSet.add(node);
                generalizationChildren.add(this.getFirstChild(node));
            } else if (this.isSplitNode(node)) {
                splitSet.add(this.getFirstSplitEdge(node).getEndNode());
            } else if (this.isSuccessNode(node)) {
                successSet.add(node);
            }
        }
        return new NodeSets(
            instanceSet,
            generalizationSet,
            successSet,
            splitSet,
            instanceChildren,
            generalizationChildren);
    }

    public Set<Edge<AbstractInferenceRule, PrologAbstractState>> getNonInstanceOutEdges(Node<PrologAbstractState> node) {
        Set<Edge<AbstractInferenceRule, PrologAbstractState>> res =
            new LinkedHashSet<Edge<AbstractInferenceRule, PrologAbstractState>>();
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (!(edge.getObject().rule() == AbstractInferenceRules.INSTANCE)) {
                res.add(edge);
            }
        }
        return res;
    }

    public Set<Node<PrologAbstractState>> getParallelNodes() {
        Set<Node<PrologAbstractState>> res = new LinkedHashSet<Node<PrologAbstractState>>();
        for (Node<PrologAbstractState> node : this.getNodes()) {
            if (this.isParallelNode(node)) {
                res.add(node);
            }
        }
        return res;
    }

    public Node<PrologAbstractState> getParent(Node<PrologAbstractState> node) {
        if (!node.equals(this.getRoot())) {
            for (Node<PrologAbstractState> in : this.getIn(node)) {
                if (!(this.getEdge(in, node).getObject().rule() == AbstractInferenceRules.INSTANCE)) {
                    return in;
                }
            }
        }
        return null;
    }

    /**
     * @return the program
     */
    public PrologProgram getProgram() {
        return this.program;
    }

    /**
     * @return the query
     */
    public PrologTerm getQuery() {
        return this.getRoot().getObject().getHeadOfState().getTerm();
    }

    /**
     * @return
     */
    public Node<PrologAbstractState> getRoot() {
        return this.root;
    }

    public Set<Node<PrologAbstractState>> getSplitNodes() {
        Set<Node<PrologAbstractState>> res = new LinkedHashSet<Node<PrologAbstractState>>();
        for (Node<PrologAbstractState> node : this.getNodes()) {
            if (this.isSplitNode(node)) {
                res.add(node);
            }
        }
        return res;
    }

    public Set<Node<PrologAbstractState>> getSuccessNodes() {
        Set<Node<PrologAbstractState>> res = new LinkedHashSet<Node<PrologAbstractState>>();
        for (Node<PrologAbstractState> node : this.getNodes()) {
            if (this.isSuccessNode(node)) {
                res.add(node);
            }
        }
        return res;
    }

    /**
     * Gathers all relevant nodes for the termination transformation and returns them in a TermNodeSets object.
     * @param aborter For abortions...
     * @return A TermNodeSets object containing all relevant nodes for the termination transformation.
     * @throws AbortionException If it is aborted...
     */
    public TermNodeSets getTermNodeSetsForPaths(Abortion aborter) throws AbortionException {
        Set<Node<PrologAbstractState>> instanceSet = new LinkedHashSet<Node<PrologAbstractState>>();
        Set<Node<PrologAbstractState>> splitSet = new LinkedHashSet<Node<PrologAbstractState>>();
        Set<Node<PrologAbstractState>> successSet = new LinkedHashSet<Node<PrologAbstractState>>();
        Set<Node<PrologAbstractState>> instanceChildren = new LinkedHashSet<Node<PrologAbstractState>>();
        for (Node<PrologAbstractState> node : this.getNodes()) {
            if (this.isInstanceNode(node) || this.isGeneralizationNode(node)) {
                instanceSet.add(node);
                instanceChildren.add(this.getFirstChild(node));
            } else if (this.isSplitNode(node)) {
                splitSet.add(node);
            } else if (this.isSuccessNode(node)) {
                successSet.add(node);
            }
        }
        return new TermNodeSets(instanceSet, successSet, splitSet, instanceChildren);
    }

    /**
     * Checks the constant successes criterion (CSC) for the specified node.
     * This criterion is only sufficient, not necessary.
     * @param node The node to check.
     * @param aborterForCSC For abortions...
     * @return True if the specified node satisfies the CSC. False otherwise.
     * @throws AbortionException If it is aborted...
     */
    public boolean hasConstantSuccesses(Node<PrologAbstractState> node, Abortion aborterForCSC)
    throws AbortionException {
        return this.hasConstantSuccesses(node, new LinkedHashSet<Node<PrologAbstractState>>(), aborterForCSC);
    }

    /**
     * Checks the constant successes criterion (CSC) for the specified node.
     * This criterion is only sufficient, not necessary.
     * @param node The node to check.
     * @param visitedForCSC A set of already visited nodes.
     * @param aborterForCSC For abortions...
     * @return True if the specified node has already been visited or if it
     *         satisfies the CSC. False otherwise.
     * @throws AbortionException If it is aborted...
     */
    public boolean hasConstantSuccesses(
        Node<PrologAbstractState> node,
        Set<Node<PrologAbstractState>> visitedForCSC,
        Abortion aborterForCSC
    ) throws AbortionException {
        aborterForCSC.checkAbortion();
        if (visitedForCSC.contains(node)) {
            return true;
        }
        // else the node has not been visited yet
        if (this.isSuccessNode(node)) {
            if (this.canReachNode(node, node, aborterForCSC)) {
                return false;
            } else {
                return this.recurseCriterion(node, visitedForCSC, false, aborterForCSC);
            }
        } else if (this.isParallelNode(node)) {
            if (this.canReachNode(node, node, aborterForCSC)) {
                return !this.canReachSuccess(node, aborterForCSC);
            } else {
                return this.recurseCriterion(node, visitedForCSC, false, aborterForCSC);
            }
        } else if (this.isSplitNode(node)) {
            if (!this.canReachSuccess(this.getLastChild(node), aborterForCSC)
                || !this.canReachSuccess(this.getFirstChild(node), aborterForCSC))
            {
                return true;
            } else if (this.canReachNode(node, node, aborterForCSC)) {
                if (this.isDeterministic(
                    this.getFirstChild(node),
                    new LinkedHashSet<Node<PrologAbstractState>>(),
                    aborterForCSC))
                {
                    final Set<Node<PrologAbstractState>> newSet = new LinkedHashSet<Node<PrologAbstractState>>(visitedForCSC);
                    newSet.add(node);
                    return this.hasConstantSuccesses(this.getLastChild(node), newSet, aborterForCSC);
                } else if (this.isDeterministic(
                    this.getLastChild(node),
                    new LinkedHashSet<Node<PrologAbstractState>>(),
                    aborterForCSC))
                {
                    final Set<Node<PrologAbstractState>> newSet = new LinkedHashSet<Node<PrologAbstractState>>(visitedForCSC);
                    newSet.add(node);
                    return this.hasConstantSuccesses(this.getFirstChild(node), newSet, aborterForCSC);
                } else {
                    return false;
                }
            } else {
                return this.recurseCriterion(node, visitedForCSC, false, aborterForCSC);
            }
        } else {
            return this.recurseCriterion(node, visitedForCSC, false, aborterForCSC);
        }
    }

    public boolean isArithCompNode(Node<PrologAbstractState> node) {
        assert this.contains(node);
        if(this.getOut(node).isEmpty()) {
            return false;
        }
        /* We only examine the first outgoing edge from the node since this
         * tells us enough about the type of the node */
        final AbstractInferenceRules ruleType = this.getOutEdges(node).iterator().next().getObject().rule();
        return
            ruleType == AbstractInferenceRules.ARITHCOMP_ERROR
            || ruleType == AbstractInferenceRules.ARITHCOMP_SUCCESS
            || ruleType == AbstractInferenceRules.ARITHCOMP_FAIL;
    }

    public boolean isAtomicCaseNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isAtomicFailNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isBacktrackNode(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.BACKTRACK) {
                return true;
            }
            break;
        }
        return false;
    }

    public boolean isBacktrackSecond(Node<PrologAbstractState> node) {
        return this.isEvalNode(node)
            || this.isParallelNode(node)
            || this.isUnifyCaseNode(node)
            || this.isAtomicCaseNode(node)
            || this.isCompoundCaseNode(node)
            || this.isEqualsCaseNode(node)
            || this.isNonvarCaseNode(node);
    }

    public boolean isCallNode(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.CALL) {
                return true;
            }
            break;
        }
        return false;
    }

    public boolean isCaseNode(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.CASE) {
                return true;
            }
            break;
        }
        return false;
    }

    public boolean isCompoundCaseNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isCompoundFailNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isCutNode(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.CUT) {
                return true;
            }
            break;
        }
        return false;
    }

    /**
     * Checks the determinacy criterion (DC) for the specified node. This
     * criterion is only sufficient, not necessary.
     * @param node The node to consider.
     * @param aborter For abortions...
     * @return True if the specified node satisfies the DC. False otherwise.
     * @throws AbortionException If it is aborted...
     */
    public boolean isDeterministic(Node<PrologAbstractState> node, Abortion aborter) throws AbortionException {
        return this.isDeterministic(node, new LinkedHashSet<Node<PrologAbstractState>>(), aborter);
    }

    public boolean isDisjunctionNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isEqualsCaseNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isEqualsFailNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isEvalNode(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.EVAL) {
                return true;
            }
            break;
        }
        return false;
    }

    public boolean isFailNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isFailureNode(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.FAILURE) {
                return true;
            }
            break;
        }
        return false;
    }

    public boolean isGeneralizationNode(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.GENERALIZATION) {
                return true;
            }
            break;
        }
        return false;
    }

    public boolean isIfThenElseNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isIfThenNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isInstanceNode(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.INSTANCE) {
                return true;
            }
            break;
        }
        return false;
    }

    public boolean isIntroducing(Node<PrologAbstractState> node) {
        return
            this.isCaseNode(node)
            || this.isCallNode(node)
            || this.isDisjunctionNode(node)
            || this.isIfThenNode(node)
            || this.isIfThenElseNode(node)
            || this.isNotNode(node)
            || this.isRepeatNode(node);
    }

    public boolean isIsNode(Node<PrologAbstractState> node) {
        assert this.contains(node);
        if (this.getOut(node).isEmpty()) {
            return false;
        }
        /* We only examine the first outgoing edge from the node since this
         * tells us enough about the type of the node */
        final AbstractInferenceRules ruleType = this.getOutEdges(node).iterator().next().getObject().rule();
        return
            ruleType == AbstractInferenceRules.IS_ERROR
            || ruleType == AbstractInferenceRules.IS_SUCCESS
            || ruleType == AbstractInferenceRules.IS_FAIL;
    }

    /**
     * @param node
     * @return
     */
    public boolean isLeaf(Node<PrologAbstractState> node, boolean instanceLeaves) {
        final Set<Edge<AbstractInferenceRule, PrologAbstractState>> edges = this.getOutEdges(node);
        if (edges == null) {
            return true;
        } else {
            if (!instanceLeaves && !edges.isEmpty()) {
                return false;
            }
            for (Edge<AbstractInferenceRule, PrologAbstractState> edge : edges) {
                if (!(edge.getObject().rule() == AbstractInferenceRules.INSTANCE)) {
                    return false;
                }
            }
            return true;
        }
    }

    public PrologTerm isNondeterministic(Node<PrologAbstractState> node, Abortion aborter) {
        // TODO
        return null;
    }

    public boolean isNonvarCaseNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isNonvarFailNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isNotNode(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.NOT) {
                return true;
            }
            break;
        }
        return false;
    }

    public boolean isNoUnifyCaseNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isNoUnifyFailNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isOnlyEvalNode(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.ONLY_EVAL) {
                return true;
            }
            break;
        }
        return false;
    }

    public boolean isParallelNode(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.PARALLEL) {
                return true;
            }
            break;
        }
        return false;
    }

    public boolean isRepeatNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    /**
     * @param startNode
     * @return
     */
    public boolean isRoot(Node<PrologAbstractState> node) {
        return this.getRoot().equals(node);
    }

    public boolean isSplitNode(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.SPLIT) {
                return true;
            }
            break;
        }
        return false;
    }

    public boolean isSuccessNode(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.SUCCESS) {
                return true;
            }
            break;
        }
        return false;
    }

    public boolean isUnequalsCaseNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isUnequalsFailNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isUnifyCaseNode(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.UNIFY_CASE) {
                return true;
            }
            break;
        }
        return false;
    }

    public boolean isUnifyFailNode(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.UNIFY_FAIL) {
                return true;
            }
            break;
        }
        return false;
    }

    public boolean isUnifySuccessNode(Node<PrologAbstractState> node) {
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(node)) {
            if (edge.getObject().rule() == AbstractInferenceRules.UNIFY_SUCCESS) {
                return true;
            }
            break;
        }
        return false;
    }

    public boolean isVarCaseNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    public boolean isVarFailNode(Node<PrologAbstractState> node) {
        // TODO Auto-generated method stub
        return false;
    }

    /**
     * Checks whether there is a path from toCheck to node only consisting of instance and generalization edges.
     * @param toCheck The start node.
     * @param node The node to be reached.
     * @return True if there is no path from toCheck to node only using instance or generalization edges.
     */
    public boolean noInstanceOrGeneralizationPath(Node<PrologAbstractState> toCheck, Node<PrologAbstractState> node) {
        if (toCheck.equals(node)) {
            return false;
        }
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getOutEdges(toCheck)) {
            final AbstractInferenceRule rule = edge.getObject();
            if (
                rule.rule() == AbstractInferenceRules.INSTANCE || rule.rule() == AbstractInferenceRules.GENERALIZATION
            ) {
                if (!this.noInstanceOrGeneralizationPath(edge.getEndNode(), node)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * @param root2
     * @param node
     * @return
     */
    public boolean oneEvalBetweenOrDifferentPath(Node<PrologAbstractState> ancestor, Node<PrologAbstractState> node) {
        if (node.equals(this.getRoot())) {
            return false;
        }
        Node<PrologAbstractState> parent = this.getParent(node);
        Node<PrologAbstractState> child = node;
        while (!parent.equals(ancestor)) {
            final AbstractInferenceRule rule = this.getEdgeObject(parent, child);
            if (rule.rule() == AbstractInferenceRules.EVAL || rule.rule() == AbstractInferenceRules.ONLY_EVAL) {
                return true;
            }
            if (parent.equals(this.getRoot())) {
                return true;
            }
            child = parent;
            parent = this.getParent(child);
        }
        final AbstractInferenceRule rule = this.getEdgeObject(parent, child);
        return rule.rule() == AbstractInferenceRules.EVAL || rule.rule() == AbstractInferenceRules.ONLY_EVAL;
    }

    /**
     * @param sigma
     * @param b
     * @param c
     */
    public PrologSubstitution refreshVarNames(
        PrologTerm t,
        PrologSubstitution sigma,
        KnowledgeBase kb,
        boolean nonAbstract
    ) {
        final PrologSubstitution renaming = new PrologSubstitution();
        final PrologEvaluationGraph graph = this;
        t.applySubstitution(sigma).walk(new TermWalker() {

            @Override
            public boolean goDeeper(PrologTerm term) {
                return true;
            }

            @Override
            public boolean isApplicable(PrologTerm term) {
                return true;
            }

            @Override
            public void performAction(PrologTerm term) {
                for (int i = 0; i < term.getArity(); i++) {
                    final PrologTerm t = term.getArgument(i);
                    if (t.isAbstractVariable() && !kb.getGroundSet().contains(t)) {
                        if (!renaming.containsKey(t)) {
                            renaming.put((PrologVariable) t, graph.getFreshAbstractVariable());
                        }
                    } else if (nonAbstract && t.isNonAbstractVariable() && !kb.getFreeSet().contains(t)) {
                        if (!renaming.containsKey(t)) {
                            renaming.put((PrologVariable) t, graph.getFreshAbstractVariable());
                        }
                    }
                }
            }

        });
        return renaming;
    }

    @Override
    public boolean removeNode(Node<PrologAbstractState> node) {
        if (this.isLeaf(node, true) && !this.getRoot().equals(node)) {
            return super.removeNode(node);
        } else {
            return false;
        }
    }

    /**
     * @param newLeaf
     */
    public void removeSubTree(Node<PrologAbstractState> newLeaf) {
        final Set<Node<PrologAbstractState>> leaves = new LinkedHashSet<Node<PrologAbstractState>>();
        final Set<Node<PrologAbstractState>> innerNodes = new LinkedHashSet<Node<PrologAbstractState>>();
        for (Node<PrologAbstractState> node : this.getOut(newLeaf)) {
            if (!(this.getEdge(newLeaf, node).getObject().rule() == AbstractInferenceRules.INSTANCE)) {
                if (this.isLeaf(node, true)) {
                    leaves.add(node);
                } else {
                    innerNodes.add(node);
                }
            }
        }
        for (Node<PrologAbstractState> node : leaves) {
            this.removeNode(node);
        }
        for (Node<PrologAbstractState> node : innerNodes) {
            this.removeSubTree(node);
            this.removeNode(node);
        }
    }

    public List<Integer> slice(PrologTerm t) {
        if (PrologEvaluationGraph.META && t.isAbstractVariable()) {
            List<Integer> res = new ArrayList<Integer>();
            for (int i = 0; i < this.getProgram().getClauses().size(); i++) {
                res.add(i);
            }
            return res;
        }
        return this.getProgram().getClauseIndicesForPredicate(t.createFunctionSymbol());
    }

    /**
     * This method is used to save a graph in nice dot format.
     * Additional, it labels the edges by using the toString() method
     * of the objects stored in the edges.
     * @param showNumbers Indicates whether or not node numbers
     *                    should be shown in the node labels.
     * @return A String containing a DOT representation of this
     *         graph.
     */
    public String toInteractiveDOTwithEdges(boolean showNumbers, Map<Integer, String> nodeLabels) {
        StringBuilder t = new StringBuilder();
        t.append("digraph dp_graph {\nnode [outthreshold=100, inthreshold=100];\n");
        int maxNodeNr = 0;
        for (Node<PrologAbstractState> from : this.getNodes()) {
            final int nr = from.getNodeNumber();
            if (nr > maxNodeNr) {
                maxNodeNr = nr;
            }
            final String nodeLabel = (nodeLabels.containsKey(nr) ? nodeLabels.get(nr) : "" + nr);
            t.append(nr + " [");
            if (from.getObject() != null) {
                t.append("label=\""
                    + (showNumbers ? nodeLabel + ": " : "")
                    + this.getDOTNodeLabelText(SimpleGraph.INTERACTIVE, from)
                    + "\", ");
            }
            t.append(this.getDOTFormatForNodeLabels(SimpleGraph.INTERACTIVE, from));
            t.append("];\n");
        }
        for (Edge<AbstractInferenceRule, PrologAbstractState> edge : this.getEdges()) {
            maxNodeNr++;
            t.append(maxNodeNr
                + " [label=\""
                + this.getDOTEdgeLabelText(edge)
                + "\", "
                + this.getDOTFormatForEdgeLabels(edge)
                + "];\n");
            final String edgeFormat = this.getDOTFormatForEdges(edge);
            t.append(edge.getStartNode().getNodeNumber()
                + " -> "
                + maxNodeNr
                + " [arrowhead = none "
                + (edgeFormat == "" ? "" : ", " + edgeFormat)
                + "];\n");
            t.append(maxNodeNr
                + " -> "
                + edge.getEndNode().getNodeNumber()
                + (edgeFormat == "" ? "" : "[" + edgeFormat + "]")
                + ";\n\n");
        }
        return t.toString() + "}\n";
    }

    @Override
    public JSONObject toJSON() {
        JSONObject res = new JSONObject();
        res.put("graph", super.toJSON());
        res.put("root", this.root.getNodeNumber());
        res.put("program", JSONExportUtil.toJSON(this.program));
        return res;
    }

    //    public void show() {
    //        final JDottyGraphDialog diag =
    //            JDottyGraphDialog.create("Partial Evalutation Tree", this.toInteractiveDOTwithEdges(true));
    //        //        diag.setMinimumSize(null);
    //        //        diag.setMaximumSize(new Dimension(1024,768)); //TODO restrict size depending on screen size
    //        //        diag.setSize(1024, 768);
    //        diag.center("" + this.getRoot().getNodeNumber());
    //        diag.setVisible(true);
    //        diag.waitForClose();
    //    }
    //
    //    public void show(Map<Integer, String> nodeLabels) {
    //        final JDottyGraphDialog diag =
    //            JDottyGraphDialog.create("Partial Evalutation Tree", this.toInteractiveDOTwithEdges(true, nodeLabels));
    //        //        diag.setMinimumSize(null);
    //        //        diag.setMaximumSize(new Dimension(1024,768)); //TODO restrict size depending on screen size
    //        //        diag.setSize(1024, 768);
    //        diag.center("" + this.getRoot().getNodeNumber());
    //        diag.setVisible(true);
    //        diag.waitForClose();
    //    }
    //
    //    public void showNonModal() {
    //        final JDottyGraphDialog diag =
    //            JDottyGraphDialog.create("Partial Evalutation Tree", this.toInteractiveDOTwithEdges(true));
    //        //        diag.setMinimumSize(null);
    //        //        diag.setMaximumSize(new Dimension(1024,768)); //TODO restrict size depending on screen size
    //        //        diag.setSize(1024, 768);
    //        diag.center("" + this.getRoot().getNodeNumber());
    //        diag.setVisible(true);
    //    }
    //
    //    public void showNonModal(Map<Integer, String> nodeLabels) {
    //        final JDottyGraphDialog diag =
    //            JDottyGraphDialog.create("Partial Evalutation Tree", this.toInteractiveDOTwithEdges(true, nodeLabels));
    //        //        diag.setMinimumSize(null);
    //        //        diag.setMaximumSize(new Dimension(1024,768)); //TODO restrict size depending on screen size
    //        //        diag.setSize(1024, 768);
    //        diag.center("" + this.getRoot().getNodeNumber());
    //        diag.setVisible(true);
    //    }

    /**
     * @param nodeLabels A map from node numbers to labels.
     * @return A TikZ representation of this graph suitable for LaTeX documents.
     */
    public String toTikZ(Map<Integer, String> nodeLabels) {
        StringBuilder res = new StringBuilder();
        res.append(this.getProgram().getLatexCommandsForSymbols());
        res.append("\\begin{tikzpicture}\n");
        res.append("[node/.style={rectangle,draw=blue!50,fill=blue!20,thick,inner sep=5pt},\n");
        res.append("pre/.style={<-,thick},post/.style={->,thick,dashed}]\n");
        res.append("\\begin{scope}[node distance = 0.5 and 0.5]\n");
        Node<PrologAbstractState> rootNode = this.getRoot();
        res.append("\\node[node");
        if (nodeLabels.containsKey(rootNode)) {
            res.append(",label=\\textsc{");
            res.append(nodeLabels.get(rootNode));
            res.append("}");
        }
        res.append("] (");
        res.append(rootNode.getNodeNumber());
        res.append(")\n");
        res.append("  {$");
        res.append(rootNode.getObject().toLaTeX());
        res.append("$};\n");
        Queue<Triple<Node<PrologAbstractState>, Node<PrologAbstractState>, Integer>> todo =
            new ArrayDeque<Triple<Node<PrologAbstractState>, Node<PrologAbstractState>, Integer>>();
        Set<Node<PrologAbstractState>> children = this.getOut(rootNode);
        int childNumber = 0;
        if (children.size() > 1) {
            childNumber++;
        }
        for (Node<PrologAbstractState> child : children) {
            todo.offer(new Triple<Node<PrologAbstractState>, Node<PrologAbstractState>, Integer>(rootNode, child, childNumber));
            childNumber++;
        }
        Set<Node<PrologAbstractState>> done = new LinkedHashSet<Node<PrologAbstractState>>();
        done.add(rootNode);
        while (!todo.isEmpty()) {
            Triple<Node<PrologAbstractState>, Node<PrologAbstractState>, Integer> next = todo.poll();
            if (done.contains(next.y)) {
                continue;
            }
            if (!done.contains(next.x) || this.isInstanceNode(next.y) && !done.contains(this.getFirstChild(next.y))) {
                todo.offer(next);
                continue;
            }
            res.append(this.toTikZ(next.x, next.y, next.z, nodeLabels));
            done.add(next.y);
            childNumber = 0;
            children = this.getOut(next.y);
            if (children.size() > 1) {
                childNumber++;
            }
            for (Node<PrologAbstractState> child : children) {
                todo.offer(new Triple<Node<PrologAbstractState>, Node<PrologAbstractState>, Integer>(next.y, child, childNumber));
                childNumber++;
            }
        }
        res.append("\\end{scope}\n");
        res.append("\\end{tikzpicture}\n");
        return res.toString();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Utility.Graph.SimpleGraph#getDOTFormatForEdgeLabels(aprove.verification.oldframework.Utility.Graph.Edge)
     */
    @Override
    protected String getDOTFormatForEdgeLabels(Edge<AbstractInferenceRule, PrologAbstractState> edge) {
        String color = "white";
        switch (edge.getObject().rule()) {
        case EVAL:
            color = ((EvalRule) edge.getObject()).getSubstitution() == null ? "lightgreen" : "lightblue";
            break;
        case UNIFY_CASE:
            color = ((UnifyCaseRule) edge.getObject()).getSubstitution() == null ? "lightgreen" : "lightblue";
            break;
        case IS_CASE:
            color = ((IsCaseRule) edge.getObject()).getSubstitution() == null ? "lightgreen" : "lightblue";
            break;
        case ARITHCOMP_CASE:
            color = ((ArithCompCaseRule) edge.getObject()).isFail() ? "lightgreen" : "lightblue";
            break;
        case ONLY_EVAL:
        case UNIFY_SUCCESS:
        case IS_SUCCESS:
        case ARITHCOMP_SUCCESS:
            color = "lightblue";
            break;
        case CASE:
        case CALL:
        case NOT:
            color = "lightcyan";
            break;
        case PARALLEL:
        case SPLIT:
        case GENERALIZATION:
            color = "violet";
            break;
        case INSTANCE:
            color = "lightgrey";
            break;
        case BACKTRACK:
        case CUT:
        case FAILURE:
        case SUCCESS:
        case UNDEFINED_ERROR:
        case UNIFY_FAIL:
        case VARIABLE_ERROR:
        case IS_ERROR:
        case ARITHCOMP_ERROR:
        case IS_FAIL:
        case ARITHCOMP_FAIL:
            color = "lightgreen";
            break;
        default:
            // should not be reachable
            throw new IllegalStateException("Unknown edge type occurred!");
        }
        return "fontsize=14, style = filled, fillcolor = " + color;
    }

    @Override
    protected String getDOTFormatForEdges(Edge<AbstractInferenceRule, PrologAbstractState> edge) {
        if (edge.getObject().rule() == AbstractInferenceRules.INSTANCE) {
            return "style=dashed";
        }
        return "";
    }

    @Override
    protected String getDOTFormatForNodeLabels(int method, Node<PrologAbstractState> node) {
        switch (method) {
        case DOT:
        case DOTDOT2:
            Set<Node<PrologAbstractState>> out = this.getOut(node);
            if (out != null && out.contains(node)) {
                return "fontsize=16, style=dashed, color=red";
            }
            return "fontsize=16";
        case SAVE:
        case EDGES:
        case DOTDOT1:
            return "fontsize=16";
        case INTERACTIVE:
            if (this.getRoot().equals(node)) {
                return "fontsize=16, style=filled, fillcolor=lightyellow, color=red";
            }
            return "fontsize=16, style=filled, fillcolor=lightyellow";
        default:
            return "";
        }
    }

    private List<KnowledgeBase> calculateCandidatesForNondeterminism(
        Node<PrologAbstractState> node,
        Abortion aborter
    ) throws AbortionException {
        // TODO regard substitutions!
        aborter.checkAbortion();
        if (this.isSuccessNode(node)) {
            final List<KnowledgeBase> success = this.isSuccessful(this.getFirstChild(node), aborter);
            if (!success.isEmpty()) {
                final List<KnowledgeBase> res = new ArrayList<KnowledgeBase>();
                final KnowledgeBase nodeKB = node.getObject().getKnowledgeBase();
                for (KnowledgeBase kb : success) {
                    res.add(kb.union(nodeKB));
                }
                return res;
            }
            // else fall through
        } else if (this.isSplitNode(node)) {
            final Node<PrologAbstractState> left = this.getFirstChild(node);
            final Node<PrologAbstractState> right = this.getLastChild(node);
            final List<KnowledgeBase> sucRight = this.isSuccessful(right, aborter);
            final List<KnowledgeBase> sucLeft = this.isSuccessful(left, aborter);
            if (!sucRight.isEmpty() && !sucLeft.isEmpty()) {
                final List<KnowledgeBase> res = new ArrayList<KnowledgeBase>();
                final List<KnowledgeBase> nondetLeft = this.calculateCandidatesForNondeterminism(left, aborter);
                final KnowledgeBase nodeKB = node.getObject().getKnowledgeBase();
                if (!nondetLeft.isEmpty()) {
                    for (KnowledgeBase kb : nondetLeft) {
                        for (KnowledgeBase suc : sucRight) {
                            res.add(kb.union(suc).union(nodeKB));
                        }
                    }
                }
                final List<KnowledgeBase> nondetRight = this.calculateCandidatesForNondeterminism(right, aborter);
                if (!nondetRight.isEmpty()) {
                    for (KnowledgeBase kb : nondetRight) {
                        for (KnowledgeBase suc : sucLeft) {
                            res.add(kb.union(suc).union(nodeKB));
                        }
                    }
                }
                return res;
            }
            // else fall through
        } else if (this.isParallelNode(node)) {
            //TODO
        } else {
            // covers all rules with only one successor and which do not change the KB
            return this.calculateCandidatesForNondeterminism(this.getFirstChild(node), aborter);
        }
        // fall through
        return Collections.EMPTY_LIST;
    }

    /**
     * Computes reachability in a graph.
     * @param node The start node to consider.
     * @param target The target node to consider.
     * @param visited A set of already visited nodes.
     * @param aborter For abortions...
     * @return True if <code>node</code> can reach <code>target</code> in
     *         this graph via a non-empty path.
     * @throws AbortionException If it is aborted...
     */
    private boolean canReachNode(
        Node<PrologAbstractState> node,
        Node<PrologAbstractState> target,
        Set<Node<PrologAbstractState>> visited,
        Abortion aborter
    ) throws AbortionException {
        if (!visited.contains(node)) {
            visited.add(node);
            for (Node<PrologAbstractState> child : this.getOut(node)) {
                if (child.equals(target)) {
                    return true;
                }
                aborter.checkAbortion();
                if (this.canReachNode(child, target, visited, aborter)) {
                    return true;
                }
            } // fall through
        }
        return false;
    }

    /**
     * Computes reachability of any SUCCESS node.
     * @param node The start node to consider.
     * @param visited A set of already visited states.
     * @param aborter For abortions...
     * @return True if <code>node</code> can reach any SUCCESS node in
     *         this graph.
     * @throws AbortionException If it is aborted...
     */
    private boolean canReachSuccess(
        Node<PrologAbstractState> node,
        Set<Node<PrologAbstractState>> visited,
        Abortion aborter
    ) throws AbortionException {
        if (this.isSuccessNode(node)) {
            return true;
        } else if (!visited.contains(node)) {
            visited.add(node);
            for (Node<PrologAbstractState> child : this.getOut(node)) {
                aborter.checkAbortion();
                if (this.canReachSuccess(child, visited, aborter)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Checks the determinacy criterion (DC) for the specified node. This
     * criterion is only sufficient, not necessary.
     * @param node The node to consider.
     * @param visitedForDC A set of already visited nodes.
     * @param aborterForDC For abortions...
     * @return True if the specified node has already been visited or if it
     *         satisfies the DC. False otherwise.
     * @throws AbortionException If it is aborted...
     */
    private boolean isDeterministic(
        Node<PrologAbstractState> node,
        Set<Node<PrologAbstractState>> visitedForDC,
        Abortion aborterForDC
    ) throws AbortionException {
        aborterForDC.checkAbortion();
        if (visitedForDC.contains(node)) {
            return true;
        }
        // else the node has not been visited yet
        if (this.isParallelNode(node)) {
            if (this.canReachNode(node, node, aborterForDC)) {
                return !this.canReachSuccess(node, aborterForDC);
            } else if (this.canReachSuccess(this.getFirstChild(node), aborterForDC)
                && this.canReachSuccess(this.getLastChild(node), aborterForDC))
            {
                return false;
            } else {
                return this.recurseCriterion(node, visitedForDC, true, aborterForDC);
            }
        } else if (this.isSuccessNode(node)) {
            if (this.canReachNode(node, node, aborterForDC)) {
                return false;
            } else {
                return this.recurseCriterion(node, visitedForDC, true, aborterForDC);
            }
        } else if (this.isSplitNode(node)
            && (!this.canReachSuccess(this.getLastChild(node), aborterForDC) || !this.canReachSuccess(
                this.getFirstChild(node),
                aborterForDC)))
        {
            return true;
        } else {
            return this.recurseCriterion(node, visitedForDC, true, aborterForDC);
        }
    }

    private List<KnowledgeBase> isSuccessful(Node<PrologAbstractState> node, Abortion aborter) {
        // TODO Auto-generated method stub
        return null;
    }

    /**
     * Just recurses the respective criterion on the successor nodes. This method just joins common code for both
     * criteria.
     * @param node The node to check for the criterion.
     * @param visited The set of already visited nodes.
     * @param deterministic Flag to indicate whether the determinacy or constant successes criterion is to be recursed.
     * @param aborter For abortions...
     * @return True, if the recursive cases all satisfy the respective criterion.
     * @throws AbortionException If it is aborted...
     */
    private boolean recurseCriterion(
        Node<PrologAbstractState> node,
        Set<Node<PrologAbstractState>> visited,
        boolean deterministic,
        Abortion aborter
    ) throws AbortionException {
        final Set<Node<PrologAbstractState>> newSet = new LinkedHashSet<Node<PrologAbstractState>>(visited);
        newSet.add(node);
        if (deterministic) {
            for (Node<PrologAbstractState> child : this.getOut(node)) {
                if (!this.isDeterministic(child, new LinkedHashSet<Node<PrologAbstractState>>(newSet), aborter)) {
                    return false;
                }
            }
        } else {
            for (Node<PrologAbstractState> child : this.getOut(node)) {
                if (!this.hasConstantSuccesses(child, new LinkedHashSet<Node<PrologAbstractState>>(newSet), aborter)) {
                    return false;
                }
            }
        }
        return true;
    }

    private String toTikZ(
        Node<PrologAbstractState> origin,
        Node<PrologAbstractState> node,
        int childNumber,
        Map<Integer, String> nodeLabels
    ) {
        StringBuilder res = new StringBuilder();
        res.append("\\node[node");
        if (nodeLabels.containsKey(node)) {
            res.append(",label=\\textsc{");
            res.append(nodeLabels.get(node));
            res.append("}");
        }
        res.append("] (");
        res.append(node.getNodeNumber());
        res.append(") [below ");
        switch (childNumber) {
        case 1:
            res.append("left ");
            break;
        case 2:
            res.append("right ");
            break;
        default:
            // do nothing
        }
        res.append("= of ");
        res.append(origin.getNodeNumber());
        switch (childNumber) {
        case 1:
            res.append(", xshift = 2cm");
            break;
        case 2:
            res.append(", xshift = -2cm");
            break;
        default:
            // do nothing
        }
        res.append("]\n");
        res.append("  {$");
        res.append(node.getObject().toLaTeX());
        res.append("$}\n");
        res.append("  edge [pre]\n");
        res.append(this
            .getEdge(origin, node)
            .getObject()
            .toLaTeX(
                origin.getObject().createSetOfAllVariables(),
                origin.getObject().getKnowledgeBase().union(node.getObject().getKnowledgeBase())));
        res.append("  (");
        res.append(origin.getNodeNumber());
        res.append(")");
        if (this.isInstanceNode(node)) {
            res.append("\n");
            res.append("  edge [post]\n");
            final Node<PrologAbstractState> successor = this.getFirstChild(node);
            res.append(this
                .getEdge(node, successor)
                .getObject()
                .toLaTeX(
                    successor.getObject().createSetOfAllVariables(),
                    node.getObject().getKnowledgeBase().union(successor.getObject().getKnowledgeBase())));
            res.append("  (");
            res.append(successor.getNodeNumber());
            res.append(")");
        }
        res.append(";\n");
        return res.toString();
    }

    /**
     * @return The factory to build SMT solvers.
     */
    public SMTSolverFactory getSMTFactory() {
        return this.smtFactory;
    }

}
