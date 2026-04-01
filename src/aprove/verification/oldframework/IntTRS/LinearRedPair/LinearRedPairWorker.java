package aprove.verification.oldframework.IntTRS.LinearRedPair;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.LinearRedPair.LinearRedPairProcessor.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Such a worker is spawned by the processor to ensure thread safeness.
 * @author Matthias Hoelzel
 *
 */
public class LinearRedPairWorker {
    /** Set of rules */
    private Set<IGeneralizedRule> rules;

    /** Set of result-rules */
    private final Set<IGeneralizedRule> resultRules;

    /** Set of LCS */
    private final LinkedList<LCS> lcss;

    /** Original rules */
    private final LinkedHashMap<IGeneralizedRule, IGeneralizedRule> origin;

    /** Generates unused names */
    private final FreshNameGenerator ng;

    /** Proof to be completed */
    private final LinearRankingProof proof;

    /** Some aborter */
    private final Abortion aborter;

    /** Is true if we could simplify the given problem */
    private boolean hasChanged;

    /** Current arguments */
    private final Arguments arguments;

    /**
     * It is a constructor; initialize the fields.
     * @param prob the current problem
     * @param lrProof the proof we are going to create
     * @param args the current arguments
     * @param abortion some aborter
     */
    public LinearRedPairWorker(
        final IRSProblem prob,
        final LinearRankingProof lrProof,
        final Arguments args,
        final Abortion abortion)
    {
        this.rules = prob.getRules();
        this.resultRules = new LinkedHashSet<>(this.rules.size());
        this.lcss = new LinkedList<>();
        this.ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        this.origin = new LinkedHashMap<>();
        this.arguments = args;
        this.aborter = abortion;
        this.proof = lrProof;
    }

    /**
     * Starts the whole process.
     * @return a transformed problem
     * @throws AbortionException can be aborted
     */
    public IRSProblem work() throws AbortionException {
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("linear");
            l.logln("Here are the rules: ");
            for (final IGeneralizedRule r : this.rules) {
                l.logln(r);
            }
            l.logln();
        }

        this.prepareRules();
        this.aborter.checkAbortion();
        if (this.arguments.exportPreparedRules) {
            this.proof.setPreparedRules(this.rules);
        }

        this.createLCSs();
        this.aborter.checkAbortion();
        if (this.arguments.exportLCSs) {
            this.proof.setLCSs(this.lcss);
        }

        this.createResult();
        this.aborter.checkAbortion();
        if (Globals.DEBUG_MATTHIAS) {
            DebugLogger.finishLog("linear");
        }

        return new IRSProblem(ImmutableCreator.create(this.resultRules));
    }

    /**
     * Getter for hasChanged. This method returns true, if and only if
     * the worker could drop some rules.
     * @return a boolean value
     */
    public boolean hasChanged() {
        return this.hasChanged;
    }

    /**
     * Prepares the rules.
     */
    private void prepareRules() {
        final RulePreparation rp = new RulePreparation(this.ng);
        Set<IGeneralizedRule> current = rp.prepare(this.rules);

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("linear");
            l.logln("Initial preparation: ");
            for (final IGeneralizedRule r : current) {
                l.logln(r);
            }
            l.logln();
        }

        current = this.createRightVariables(current);

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("linear");
            l.logln("Created right variables: ");
            for (final IGeneralizedRule r : current) {
                l.logln(r);
            }
            l.logln();
        }

        current = this.killFreeVariables(current);

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("linear");
            l.logln("Killed free variables: ");
            for (final IGeneralizedRule r : current) {
                l.logln(r);
            }
            l.logln();
        }

        current = this.balanceVariables(current);

        if (this.arguments.useConstants) {
            current = this.addOnes(current);
            if (Globals.DEBUG_MATTHIAS) {
                final DebugLogger l = DebugLogger.getLogger("linear");
                l.logln("Added ones: ");
                for (final IGeneralizedRule r : current) {
                    l.logln(r);
                }
                l.logln();
            }
        }

        this.rules = current;

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("linear");
            l.logln("Here are the prepared rules: ");
            for (final IGeneralizedRule r : this.rules) {
                l.logln(r);
            }
            l.logln();
        }
    }

    /**
     * Replaces terms on right sides by new variables.
     * @param rs set of rules
     * @return another set of rules
     */
    private Set<IGeneralizedRule> createRightVariables(final Set<IGeneralizedRule> rs) {
        final Set<IGeneralizedRule> result = new LinkedHashSet<>(rs.size());
        for (final IGeneralizedRule rule : rs) {
            final TRSFunctionApplication right = (TRSFunctionApplication) rule.getRight();
            TRSTerm cond = rule.getCondTerm();
            final ImmutableList<TRSTerm> args = right.getArguments();
            final ArrayList<TRSTerm> newArgs = new ArrayList<>(args.size());
            for (final TRSTerm arg : args) {
                final TRSVariable newVariable = TRSTerm.createVariable(this.ng.getFreshName("y", false));
                final TRSTerm newCondition = ToolBox.buildEq(newVariable, arg);
                cond = ToolBox.buildAnd(cond, newCondition);
                newArgs.add(newVariable);
            }
            final TRSFunctionApplication newRight = TRSTerm.createFunctionApplication(right.getRootSymbol(), newArgs);
            final IGeneralizedRule newRule = IGeneralizedRule.create(rule.getLeft(), newRight, cond);
            this.registerOrigin(newRule, rule);
            result.add(newRule);
        }
        return result;
    }

    /**
     * Removes free variables by pushing them into the parameter list.
     * @param rs set of IGeneralizedRules
     * @return set of transformed IGeneralizedRules
     */
    private Set<IGeneralizedRule> killFreeVariables(final Set<IGeneralizedRule> rs) {
        Set<IGeneralizedRule> current = rs;
        boolean done = false;
        while (!done) {
            FunctionSymbol toExtend = null;
            IGeneralizedRule problemRule = null;
            LinkedHashSet<TRSVariable> freeVars = null;
            done = true;
            for (final IGeneralizedRule r : current) {
                final LinkedHashSet<TRSVariable> freeVariables = ToolBox.getFreeVariables(r);
                if (freeVariables.isEmpty()) {
                    continue;
                }
                toExtend = r.getLeft().getRootSymbol();
                problemRule = r;
                freeVars = freeVariables;
                done = false;
                break;
            }
            if (toExtend != null) {
                final Set<IGeneralizedRule> nextRules = new LinkedHashSet<>();
                for (final IGeneralizedRule r : current) {
                    final TRSFunctionApplication left = r.getLeft();
                    final FunctionSymbol leftSymbol = left.getRootSymbol();
                    final ImmutableList<TRSTerm> leftArgs = left.getArguments();
                    final TRSFunctionApplication right = (TRSFunctionApplication) r.getRight();
                    final FunctionSymbol rightSymbol = right.getRootSymbol();
                    final int n = freeVars.size();
                    final TRSFunctionApplication newLeft;
                    if (r == problemRule) {
                        final ArrayList<TRSTerm> newLeftArgs = new ArrayList<>(leftArgs.size() + n);
                        newLeftArgs.addAll(leftArgs);
                        newLeftArgs.addAll(freeVars);
                        newLeft =
                            TRSTerm.createFunctionApplication(
                                FunctionSymbol.create(leftSymbol.getName(), newLeftArgs.size()),
                                newLeftArgs
                            );
                    } else {
                        if (left.getRootSymbol().equals(toExtend)) {
                            newLeft = ToolBox.addVariables(left, n, this.ng);
                        } else {
                            newLeft = left;
                        }
                    }
                    final TRSFunctionApplication newRight;
                    if (rightSymbol.equals(toExtend)) {
                        newRight = ToolBox.addVariables(right, n, this.ng);
                    } else {
                        newRight = right;
                    }
                    final IGeneralizedRule newRule = IGeneralizedRule.create(newLeft, newRight, r.getCondTerm());
                    this.registerOrigin(newRule, r);

                    nextRules.add(newRule);
                }
                current = nextRules;
            }
        }

        return current;
    }

    /**
     * Needed to ensure that the matrices we are going to build
     * have the same format. It balances the arities of the outermost function
     * symbols.
     * @param rs set of IGeneralizedRules
     * @return set of transformed IGeneralizedRules
     */
    private Set<IGeneralizedRule> balanceVariables(final Set<IGeneralizedRule> rs) {
        int n = 0;
        for (final IGeneralizedRule r : rs) {
            final TRSFunctionApplication oldLeft = r.getLeft();
            final TRSFunctionApplication oldRight = (TRSFunctionApplication) r.getRight();

            final int m = oldLeft.getArguments().size();
            final int k = oldRight.getArguments().size();
            n = m > n ? m : n;
            n = k > n ? k : n;
        }

        final Set<IGeneralizedRule> result = new LinkedHashSet<>(rs.size());
        for (final IGeneralizedRule r : rs) {
            final TRSFunctionApplication oldLeft = r.getLeft();
            final TRSFunctionApplication oldRight = (TRSFunctionApplication) r.getRight();

            final int m = oldLeft.getArguments().size();
            final TRSFunctionApplication newLeft = ToolBox.addVariables(oldLeft, n - m, this.ng);

            final int k = oldRight.getArguments().size();
            final TRSFunctionApplication newRight = ToolBox.addVariables(oldRight, n - k, this.ng);

            final IGeneralizedRule newRule = IGeneralizedRule.create(newLeft, newRight, r.getCondTerm());
            this.registerOrigin(newRule, r);
            result.add(newRule);
        }

        return result;
    }

    /**
     * Takes a set of rules and adds some variables, which have to be one.
     * @param rs set of rules
     * @return another set of rules
     */
    private Set<IGeneralizedRule> addOnes(final Set<IGeneralizedRule> rs) {
        final LinkedHashSet<IGeneralizedRule> result = new LinkedHashSet<>(rs.size());

        for (final IGeneralizedRule iRule : rs) {
            final TRSFunctionApplication leftSide = iRule.getLeft();
            final TRSFunctionApplication rightSide = ((TRSFunctionApplication) iRule.getRight());
            TRSTerm condition = iRule.getCondTerm();

            final TRSVariable leftOne = TRSTerm.createVariable(this.ng.getFreshName("c", false));
            final TRSVariable rightOne = TRSTerm.createVariable(this.ng.getFreshName("c", false));

            final ArrayList<TRSTerm> leftArgs = new ArrayList<>(leftSide.getArguments().size() + 1);
            final ArrayList<TRSTerm> rightArgs = new ArrayList<>(leftSide.getArguments().size() + 1);

            leftArgs.add(leftOne);
            leftArgs.addAll(leftSide.getArguments());

            rightArgs.add(rightOne);
            rightArgs.addAll(rightSide.getArguments());

            condition =
                ToolBox.buildAnd(condition, ToolBox.buildEq(
                    leftOne,
                    ToolBox.PREDEFINED.getIntTerm(BigIntImmutable.ONE, DomainFactory.INTEGERS)));
            condition =
                ToolBox.buildAnd(
                    condition,
                    ToolBox.buildEq(
                        rightOne,
                        ToolBox.PREDEFINED.getIntTerm(BigIntImmutable.ONE, DomainFactory.INTEGERS)));

            final FunctionSymbol newLeftSym =
                FunctionSymbol.create(leftSide.getRootSymbol().getName(), leftArgs.size());
            final FunctionSymbol newRightSym =
                FunctionSymbol.create(rightSide.getRootSymbol().getName(), rightArgs.size());

            final IGeneralizedRule resultRule =
                IGeneralizedRule.create(
                    TRSTerm.createFunctionApplication(newLeftSym, leftArgs),
                    TRSTerm.createFunctionApplication(newRightSym, rightArgs),
                    condition);
            this.registerOrigin(resultRule, iRule);
            result.add(resultRule);
        }

        return result;
    }

    /**
     * Registers transformation step, because later we want to return the original
     * rules.
     * @param from the new rule
     * @param to the old rule
     */
    private void registerOrigin(final IGeneralizedRule from, final IGeneralizedRule to) {
        if (from == to || from.equals(to)) {
            return;
        }

        this.origin.put(from, to);
    }

    /**
     * Creates the transition matrices.
     * @throws AbortionException
     */
    private void createLCSs() throws AbortionException {
        for (final IGeneralizedRule rule : this.rules) {
            final RuleToLCS rtl = new RuleToLCS(rule, this.ng, this.aborter);
            final LCS lcs = rtl.translate();
            this.lcss.add(lcs);
        }
    }

    /**
     * Solve the constraints.
     * @throws AbortionException can be aborted
     */
    private void createResult() throws AbortionException {
        final AbstractLCSAnalyzer analzyer = new MRPAnalyzer(this.lcss, this.proof, this.ng, this.aborter);
        final List<LCS> resultLCSs = analzyer.solve();

        // Find corresponding result rules:
        for (final LCS lcs : resultLCSs) {
            final IGeneralizedRule originRule = this.getOriginRule(lcs.getOriginRule());
            this.resultRules.add(originRule);
        }

        // Pass dropped rules to the proof:
        final LinkedHashSet<IGeneralizedRule> droppedRules =
            new LinkedHashSet<>(this.rules.size() - this.resultRules.size());
        for (final LCS lcs : analzyer.getDroppedRules()) {
            droppedRules.add(this.getOriginRule(lcs.getOriginRule()));
        }
        this.proof.setDroppedRules(droppedRules);

        // The analyzer knows if some rules were dropped:
        this.hasChanged = analzyer.hasChanged();
    }

    /**
     * Returns the origin of the given rule.
     * @param rule IGeneralizedRule
     * @return IGeneralizedRule
     */
    private IGeneralizedRule getOriginRule(final IGeneralizedRule rule) {
        final IGeneralizedRule directOrigin = this.origin.get(rule);
        if (directOrigin == null || directOrigin == rule) {
            return rule;
        } else {
            return this.getOriginRule(directOrigin);
        }
    }
}
