package aprove.verification.oldframework.IntTRS.CaseAnalysis;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.CaseAnalysis.CaseAnalysisProcessor.Arguments;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.PolynomialConstraint.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Tries to find some inductive conditions. TODO: DOKU!!!
 * @author Matthias Hoelzel
 */
public class InductiveConditionFinder {
    /** The input system. */
    private final IRSwTProblem inputSystem;

    /** Transformation to a system where every rule has the form
     *  f(..) -> f(..), if this is possible.
     */
    private IRSwTProblem transformedSystem;

    /**
     * List of candidates, which may be inductive w.r.t. the input rewrite system.
     */
    private List<GEZeroCondition> candidates;

    /**
     * A condition which turns out to be inductive for the given rewrite system.
     */
    private GEZeroCondition resultCondition;

    /**
     * Gathers the constraints, which occur in the rewrite system. This is needed for
     * a heuristic which tries to identify a condition that will be eventually unsatisfied.
     * See changeTermHeuristic() for more information.
     */
    private LinkedHashSet<PolynomialConstraint> constraints;

    /** Build formulae */
    private final FormulaFactory<SMTLIBTheoryAtom> factory;

    /** Generates fresh names */
    private final FreshNameGenerator ng;

    /** Arguments */
    private final Arguments args;

    /** Aborts if our time is up. */
    private final Abortion aborter;

    /** Set of defined symbols. */
    private LinkedHashSet<FunctionSymbol> symbols;

    /** A root symbol, if it succeeds to reformulate the system with only one symbol. */
    private FunctionSymbol rootSymbol;

    /**
     * Constructor!
     * @param system input system
     * @param formFactory formula factory
     * @param abortion some aborter
     * @param gen some name generator
     */
    public InductiveConditionFinder(
        final IRSwTProblem system,
        final FormulaFactory<SMTLIBTheoryAtom> formFactory,
        final Arguments arguments,
        final Abortion abortion,
        final FreshNameGenerator gen)
    {
        this.inputSystem = system;
        this.factory = formFactory;
        this.aborter = abortion;
        this.ng = gen;
        this.args = arguments;

        assert system != null && formFactory != null && abortion != null && gen != null : "Null!";
    }

    /**
     * Tries to find a inductive (w.r.t. rewrite system) condition.
     * @return {@link GEZeroCondition}, if possible.
     * @throws AbortionException can be aborted
     */
    public GEZeroCondition getInductiveCondition() throws AbortionException {
        if (this.resultCondition == null) {
            this.findInductiveCondition();
        }

        return this.resultCondition;
    }

    /**
     * Tries to find a inductive (w.r.t. rewrite system) condition. Will be called by getInductiveCondition().
     * @throws AbortionException can be aborted
     */
    private void findInductiveCondition() throws AbortionException {
        this.candidates = new LinkedList<>();

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("indcond");
            l.logln("Finding candidates for ");
            l.logln(this.inputSystem.toString());
            l.logln();
        }

        // 1. Find symbols and analyze the loop structure
        this.findSymbols();

        // 2. Transforms rules via chaining into the form f(..) -> f(..)
        // If this step fails, then we cannot do anything.
        if (this.transformRules()) {
            this.candidateGenerationHeuristic();
        }

        // 3. Get the gold:
        this.computeInductiveCondition();

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("indcond");
            l.logln("Got the gold: ");
            l.logln(this.resultCondition);
            l.logln();
        }

        if (Globals.DEBUG_MATTHIAS) {
            DebugLogger.finishLog("indcond");
        }
    }

    /**
     * Applies some heuristic to find "good" candidates for
     * a inductive condition.
     * @throws AbortionException can be aborted
     */
    private void candidateGenerationHeuristic() throws AbortionException {
        // 1. Rewrite conditions into
        this.rewriteConditions();

        // 2. Apply change-term heuristic
        this.changeTermHeuristic();
    }

    /**
     * Computes an inductive condition. If the heuristic has produced something
     * usefull, then we take it. Otherwise we try a more systematic approach (see {@link DecreasingInterpretationFinder}).
     * @throws AbortionException can be aborted
     */
    private void computeInductiveCondition() throws AbortionException {
        // Did the heuristic produce something useful?
        if (this.transformedSystem != null) {
            for (final GEZeroCondition c : this.candidates) {
                if (this.isUseless(c, this.transformedSystem)) {
                    continue;
                }

                final InductiveChecker indCheck =
                    new InductiveChecker(c, this.transformedSystem, this.factory, this.aborter, this.ng);
                if (indCheck.check()) {
                    this.resultCondition = c;
                    break;
                }
            }
        }

        if (this.resultCondition == null) {
            // Otherwise we try a systematic approach:
            if (this.args.mode.equals(CaseAnalysisMode.ONLY_HEURISTIC)) {
                // Ok, we are not allowed to do this... bye!
                return;
            }
            final DecreasingInterpretationFinder dif =
                new DecreasingInterpretationFinder(this.inputSystem, this.factory, this.aborter, this.ng);
            final GEZeroCondition difResult = dif.findInductiveCondition();
            if (Globals.DEBUG_MATTHIAS) {
                final DebugLogger l = DebugLogger.getLogger("indcond");
                l.logln("Dif returned: ");
                l.logln(difResult);
            }
            if (difResult != null && !this.isUseless(difResult, this.inputSystem)) {
                // Check whether it is really inductive:
                final InductiveChecker ic =
                    new InductiveChecker(difResult, this.inputSystem, this.factory, this.aborter, this.ng);
                final boolean isInductive = ic.check();

                if (isInductive) {
                    // Cool, no mistake!
                    this.resultCondition = difResult;
                } else if (ic.getSMTResult().getKey() != YNM.MAYBE) {
                    assert false : "Generated non-inductive invariant:\n"
                        + difResult.toString()
                        + "\nSMT-Result: "
                        + ic.getSMTResult()
                        + "\n";
                }
            }
        }
    }

    /**
     * A condition c is useless (for our purposes), if it is always true or always wrong.
     * Then c would not provide new information, so we will discard it.
     * @param c some {@link GEZeroCondition}
     * @param system the currently used system
     * @return true or false
     */
    private boolean isUseless(final GEZeroCondition c, final IRSwTProblem system) {
        final LinkedList<Formula<SMTLIBTheoryAtom>> canSatisfyList = new LinkedList<>();
        final LinkedList<Formula<SMTLIBTheoryAtom>> canViolateList = new LinkedList<>();

        for (final IGeneralizedRule rule : system.getRules()) {
            TRSTerm conditionTerm = rule.getCondTerm();
            if (conditionTerm == null) {
                conditionTerm = ToolBox.buildTrue();
            }

            final Formula<SMTLIBTheoryAtom> leftSideSatisfiesCond =
                c.buildCorrespondingGEConstraint(rule.getLeft(), this.ng, this.factory);
            final Formula<SMTLIBTheoryAtom> leftSideSatisfiesCondNegated = this.factory.buildNot(leftSideSatisfiesCond);
            final Formula<SMTLIBTheoryAtom> ruleCondition =
                ToolBox.boolTermToSMT_QF_IA(conditionTerm, this.factory, this.ng);

            canSatisfyList.add(this.factory.buildAnd(leftSideSatisfiesCond, ruleCondition));
            canViolateList.add(this.factory.buildAnd(leftSideSatisfiesCondNegated, ruleCondition));
        }

        final Formula<SMTLIBTheoryAtom> canSatisfyCond = this.factory.buildOr(canSatisfyList);
        final Formula<SMTLIBTheoryAtom> canViolateCond = this.factory.buildOr(canViolateList);

        final SMTEngine smtEngine = new SMTLIBEngine();
        Pair<YNM, Map<String, String>> res1;
        try {
            final Abortion subAbortion = this.aborter.createChild(1000);
            res1 = smtEngine.solve(Collections.singletonList(canSatisfyCond), SMTLogic.QF_NIA, subAbortion);
        } catch (final WrongLogicException | AbortionException e) {
            // we do not care
            res1 = new Pair<>(YNM.MAYBE, null);
        }

        if (res1.x == YNM.NO) {
            return true;
        }

        Pair<YNM, Map<String, String>> res2;
        try {
            final Abortion subAbortion = this.aborter.createChild(1000);
            res2 = smtEngine.solve(Collections.singletonList(canViolateCond), SMTLogic.QF_NIA, subAbortion);
        } catch (final WrongLogicException | AbortionException e) {
            // we do not care
            res2 = new Pair<>(YNM.MAYBE, null);
        }

        return res2.x == YNM.NO;
    }

    /**
     * Rewrites the condition term into our data structures.
     * @throws AbortionException can be aborted
     */
    private void rewriteConditions() throws AbortionException {
        this.constraints = new LinkedHashSet<>();

        for (final IGeneralizedRule rule : this.transformedSystem.getRules()) {
            TRSTerm condition = rule.getCondTerm();
            condition = condition == null ? ToolBox.buildTrue() : condition;
            final List<PolynomialConstraint> polyConds =
                ToolBox.boolTermToPolynomialConstraints((TRSFunctionApplication) condition, this.ng, this.aborter);

            final FunctionSymbol sym = rule.getLeft().getRootSymbol();
            final TRSFunctionApplication stdFuncy = InductiveConditionFinder.getStandardApplication(sym);
            final Set<String> variables = InductiveConditionFinder.translateVariables(stdFuncy.getVariables());

            for (final PolynomialConstraint pc : polyConds) {
                final TRSSubstitution matcher = rule.getLeft().getMatcher(stdFuncy);
                final LinkedHashMap<String, VarPolynomial> matcherMap = this.translateMatcher(matcher);

                final VarPolynomial normalizedPoly = pc.getPolynomial().substituteVariables(matcherMap);

                if (Globals.DEBUG_MATTHIAS) {
                    final DebugLogger l = DebugLogger.getLogger("indcond");
                    l.logln("matcher = " + matcher);
                    l.logln("normalizedPoly = " + normalizedPoly);
                }

                if (variables.containsAll(normalizedPoly.getVariables())) {
                    switch (pc.getType()) {
                    case PCT_EQ:
                        this.constraints.add(new PolynomialConstraint(
                            normalizedPoly,
                            PolynomialConstraintType.PCT_GE,
                            this.ng));
                        this.constraints.add(new PolynomialConstraint(
                            normalizedPoly.negate(),
                            PolynomialConstraintType.PCT_GE,
                            this.ng));
                        break;
                    case PCT_GE:
                        this.constraints.add(new PolynomialConstraint(
                            normalizedPoly,
                            PolynomialConstraintType.PCT_GE,
                            this.ng));
                        break;
                    case PCT_LE:
                        this.constraints.add(new PolynomialConstraint(
                            normalizedPoly.negate(),
                            PolynomialConstraintType.PCT_GE,
                            this.ng));
                        break;
                    default:
                        assert false : "Default?!";
                    }
                }
            }
        }
    }

    /**
     * Turns a set of variables into a set of strings (theis names!).
     * @param variables set of variables
     * @return set of strings
     */
    private static Set<String> translateVariables(final Set<TRSVariable> variables) {
        final LinkedHashSet<String> result = new LinkedHashSet<>();
        for (final TRSVariable v : variables) {
            result.add(v.getName());
        }
        return result;
    }

    /**
     * Translates a substitution into a substitution for polynomials. (Term using +, *, - "are" polynomials)
     * @param matcher some substitution
     * @return mapping from strings to polynomials
     */
    private LinkedHashMap<String, VarPolynomial> translateMatcher(final TRSSubstitution matcher) {
        final LinkedHashMap<String, VarPolynomial> result = new LinkedHashMap<>();
        final ImmutableMap<TRSVariable, ? extends TRSTerm> matcherMap = matcher.toMap();
        for (final Entry<TRSVariable, ? extends TRSTerm> e : matcherMap.entrySet()) {
            final TRSTerm t = e.getValue();
            result.put(e.getKey().getName(), ToolBox.intTermToPolynomial(t, this.ng));
        }
        return result;
    }

    /**
     * Finds the defined symbols.
     */
    private void findSymbols() {
        this.symbols = new LinkedHashSet<>();

        for (final IGeneralizedRule rule : this.inputSystem.getRules()) {
            this.symbols.add(rule.getLeft().getRootSymbol());
            this.symbols.add(((TRSFunctionApplication) rule.getRight()).getRootSymbol());
        }

        // TODO: Analysis of loop structure!
    }

    /**
     * Tries to transformed the system into rule of the form
     * f(..) -> f(..).
     * @return false, if this is not possible
     */
    private boolean transformRules() {
        // TODO: Generalize me!!

        this.transformedSystem = new IRSwTProblem(ImmutableCreator.create(this.inputSystem.getRules()));
        if (this.symbols.size() == 1) {
            this.rootSymbol = this.symbols.iterator().next();
        }

        return this.symbols.size() == 1;
    }

    /**
     * Computes a canonical function application of the function symbol f.
     * @param sym the function symbol f
     */
    private static TRSFunctionApplication getStandardApplication(final FunctionSymbol sym) {
        final ArrayList<TRSTerm> args = new ArrayList<>(sym.getArity());
        for (int i = 0; i < sym.getArity(); i++) {
            args.add(TRSTerm.createVariable("x" + i));
        }
        return TRSTerm.createFunctionApplication(sym, args);
    }

    /**
     * Heuristic that tries to identify a condition which will eventually be unsatisfied.
     * @throws AbortionException can be aborted
     */
    private void changeTermHeuristic() throws AbortionException {
        if (this.args.mode.equals(CaseAnalysisMode.ONLY_SMT)) {
            return;
        }
        for (final PolynomialConstraint pc : this.constraints) {
            assert pc.getType().equals(PolynomialConstraintType.PCT_GE) : "Weird constraint-type!";
            final VarPolynomial vp = pc.getPolynomial();

            this.searchInductiveTerms(vp.plus(VarPolynomial.ONE).negate(), this.symbols.iterator().next().getArity());
        }
    }

    /**
     * Tries to find a reason why vp will not be >= 0 forever. If it finds such a reason, then
     * it generates a new candidate for a inductive condition.
     * @param vp some polynomial
     * @param remainingDepth some decreasing integer (to make this thing terminate eventually)
     * @throws AbortionException can be aborted
     */
    private void searchInductiveTerms(final VarPolynomial vp, final int remainingDepth) throws AbortionException {
        if (remainingDepth < 0) {
            return;
        }

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("indcond");
            l.logln("isProbablyInductive(" + vp + ", " + remainingDepth + ")");
        }

        final LinkedList<VarPolynomial> evilChangeTerms = new LinkedList<>();
        for (final IGeneralizedRule rule : this.transformedSystem.getRules()) {
            final VarPolynomial changeTerm = this.calculateChangeTerm(rule, vp);
            if (Globals.DEBUG_MATTHIAS) {
                final DebugLogger l = DebugLogger.getLogger("indcond");
                l.logln("" + rule);
                l.logln("=> " + changeTerm);
            }

            if (this.canBeLTZero(changeTerm, rule)) {
                evilChangeTerms.add(changeTerm);
            }
        }

        if (evilChangeTerms.isEmpty()) {
            // YAY! We just found another candidate:
            final LinkedHashMap<FunctionSymbol, Pair<TRSFunctionApplication, VarPolynomial>> newCandidateMap =
                new LinkedHashMap<>();
            for (final FunctionSymbol symbol : this.symbols) {
                newCandidateMap.put(
                    symbol,
                    new Pair<TRSFunctionApplication, VarPolynomial>(InductiveConditionFinder
                        .getStandardApplication(symbol), vp.minus(VarPolynomial.ONE)));
            }
            final GEZeroCondition newCandidate = new GEZeroCondition(newCandidateMap);
            this.candidates.add(newCandidate);
        } else {
            this.aborter.checkAbortion();
            // Is there any hope to deal with the bad guys?
            final TRSFunctionApplication stdFuncy = InductiveConditionFinder.getStandardApplication(this.rootSymbol);
            final Set<TRSVariable> stdVariables = stdFuncy.getVariables();
            for (final VarPolynomial uglyCT : evilChangeTerms) {
                for (final String v : uglyCT.getVariables()) {
                    if (!stdVariables.contains(TRSTerm.createVariable(v))) {
                        // Sorry, but you are just too ugly to be handled!
                        return;
                    }
                }

            }

            // Handle the bad guys via recursion:
            for (final VarPolynomial uglyCT : evilChangeTerms) {
                this.searchInductiveTerms(uglyCT, remainingDepth - 1);
            }
        }
    }

    /**
     * Computes whether or not it is possible to use a given rule with an interpretation
     * \sigma s.t. a given polynomial is negative when evaluated w.r.t. \sigma.
     * @param changeTerm some polynomial
     * @param rule some rule
     * @return true or false
     */
    private boolean canBeLTZero(final VarPolynomial changeTerm, final IGeneralizedRule rule) {
        assert changeTerm.isConcrete() : "Non-concrete terms!";
        if (changeTerm.isConstant()) {
            return changeTerm.getConstantPart().getNumericalAddend().compareTo(BigInteger.ZERO) < 0;
        }

        // Might be a difficult question -> ask the SMT-Solver about it:
        final TRSFunctionApplication stdFuncy =
            InductiveConditionFinder.getStandardApplication(rule.getLeft().getRootSymbol());
        final Map<String, VarPolynomial> matcher = this.translateMatcher(stdFuncy.getMatcher(rule.getLeft()));
        final VarPolynomial toCheck = changeTerm.substituteVariables(matcher);

        TRSTerm condition = rule.getCondTerm();
        condition = condition == null ? ToolBox.buildTrue() : condition;

        final Formula<SMTLIBTheoryAtom> formula =
            this.factory.buildAnd(
                this.factory.buildTheoryAtom(SMTLIBIntLT.create(
                    toCheck.toSMTLIB(),
                    SMTLIBIntConstant.create(BigInteger.ZERO))),
                ToolBox.boolTermToSMT_QF_IA(condition, this.factory, this.ng));

        // Ask the SMT-Solver about it:
        Pair<YNM, Map<String, String>> verdict;
        try {
            final Abortion subAbortion = this.aborter.createChild(1000);
            final SMTEngine solver = new SMTLIBEngine();
            verdict = solver.solve(Collections.singletonList(formula), SMTLogic.QF_NIA, subAbortion);
        } catch (final WrongLogicException | AbortionException e) {
            // we do not care
            verdict = new Pair<>(YNM.MAYBE, null);
        }
        return verdict.x != YNM.NO;
    }

    /**
     * Calculates the "effect term" of a given rule on a polynomial.
     * @param rule some rule
     * @param constraint some polynomial
     * @return the effect of the rule on the polynmial
     * @throws AbortionException can be aborted
     */
    private VarPolynomial calculateChangeTerm(final IGeneralizedRule rule, final VarPolynomial constraint)
        throws AbortionException
    {
        final TRSFunctionApplication left = rule.getLeft();
        final TRSFunctionApplication right = (TRSFunctionApplication) rule.getRight();
        assert left.getRootSymbol().equals(right.getRootSymbol()) : "Can't handle f(..) -> g(..)!";

        final TRSFunctionApplication funcy = InductiveConditionFinder.getStandardApplication(left.getRootSymbol());
        final LinkedHashMap<String, VarPolynomial> leftSubstitution = this.translateMatcher(funcy.getMatcher(left));

        final TRSSubstitution sub = funcy.getMatcher(right);
        final LinkedHashMap<String, VarPolynomial> rightSubstitution = new LinkedHashMap<>();
        for (final Entry<TRSVariable, ? extends TRSTerm> e : sub.toMap().entrySet()) {
            rightSubstitution.put(e.getKey().getName(), ToolBox.intTermToPolynomial(e.getValue(), this.ng));
        }

        final VarPolynomial leftInterpretation = constraint.substituteVariables(leftSubstitution, this.aborter);
        final VarPolynomial rightInterpretation = constraint.substituteVariables(rightSubstitution, this.aborter);

        final VarPolynomial changeTerm = rightInterpretation.minus(leftInterpretation);

        final LinkedHashMap<String, VarPolynomial> correctNamesSubstitution =
            this.translateMatcher(left.getMatcher(funcy));

        return changeTerm.substituteVariables(correctNamesSubstitution, this.aborter);
    }
}
