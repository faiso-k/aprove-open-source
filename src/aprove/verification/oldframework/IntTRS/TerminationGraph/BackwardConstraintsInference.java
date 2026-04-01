package aprove.verification.oldframework.IntTRS.TerminationGraph;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Takes two rules as input and generates a rule with more constraints. Please
 * note, that this algorithm is only correct for rule of an intTRS.
 * @author Matthias Hoelzel
 */
class BackwardConstraintsInference {
    /** The rule to be transformed. */
    private final IGeneralizedRule currentRule;

    /**
     * A predecessor rule of currentRule, i.e., a rule that can be used before
     * currentRule.
     */
    private final IGeneralizedRule predecessor;

    /** Generate some fresh names */
    private final FreshNameGenerator ng;

    /** List of constraints that are going to be added. */
    private final LinkedList<TRSTerm> usefulConstraints;

    /** List of variables from the right side of the predecessor to be utilized. */
    private final LinkedHashSet<TRSVariable> usefulVariables;

    /** Stores the result. */
    private IGeneralizedRule result;

    /**
     * Constructor!
     * @param current the current rule
     * @param predec predecessor rule of current rule
     * @param gen some name generator
     */
    public BackwardConstraintsInference(final IGeneralizedRule current, final IGeneralizedRule predec,
            final FreshNameGenerator gen) {
        this.currentRule = current;
        this.ng = gen;
        this.predecessor = ToolBox.renameVariablesInRule(predec, this.ng);
        this.usefulConstraints = new LinkedList<>();
        this.usefulVariables =
            new LinkedHashSet<>(current.getRootSymbol().getArity());

        assert this.currentRule.getLeft().getRootSymbol().equals(
            ((TRSFunctionApplication) this.predecessor.getRight()).getRootSymbol());
    }

    /**
     * Calculates the result rule.
     * @return currentRule with more constraints
     */
    public IGeneralizedRule calculateResult() {
        if (this.result != null) {
            return this.result;
        }
        final IGeneralizedRule renamedPredec = ToolBox.renameVariablesInRule(this.predecessor, this.ng);
        // Get right side of predecessor rule & left side of current rule:
        final TRSFunctionApplication rightSideOfPredec = (TRSFunctionApplication) renamedPredec.getRight();
        final TRSFunctionApplication leftSideOfCurrent = this.currentRule.getLeft();
        // Get the predecessor variables &
        final ImmutableList<TRSTerm> currentVariables = leftSideOfCurrent.getArguments();
        final Set<TRSVariable> predecVariables = rightSideOfPredec.getVariables();
        final TRSTerm rightCondTerm = renamedPredec.getCondTerm();
        if (rightCondTerm != null) {
            this.collectUsefulConstraints((TRSFunctionApplication)rightCondTerm, predecVariables);
        }
        final Iterator<TRSTerm> argumentIterator = rightSideOfPredec.getArguments().iterator();
        final Iterator<TRSTerm> variableIterator = currentVariables.iterator();
        TRSTerm newConstraints = this.currentRule.getCondTerm();
        if (newConstraints == null) {
            newConstraints = ToolBox.buildTrue();
        }
        while (argumentIterator.hasNext()) {
            final TRSTerm v = variableIterator.next();
            final TRSTerm arg = argumentIterator.next();
            final boolean useConstraint;
            if (
                !arg.isVariable()
                && ToolBox.PREDEFINED.isInt(((TRSFunctionApplication) arg).getRootSymbol(), DomainFactory.INTEGERS)
            ) {
                useConstraint = true;
            } else if (this.usefulVariables.containsAll((arg.getVariables()))) {
                useConstraint = true;
            } else {
                useConstraint = false;
            }
            if (useConstraint) {
                newConstraints = ToolBox.buildAnd(ToolBox.buildEq(v, arg), newConstraints);
            }
        }
        for (final TRSTerm t : this.usefulConstraints) {
            newConstraints = ToolBox.buildAnd(newConstraints, t);
        }
        this.result = IGeneralizedRule.create(this.currentRule.getLeft(), this.currentRule.getRight(), newConstraints);
        return this.result;
    }

    /**
     * Collects the "useful" constraints.
     * @param currentCondition the current condition term
     * @param predecVariables allowed variables
     */
    private void collectUsefulConstraints(final TRSFunctionApplication currentCondition,
        final Set<TRSVariable> predecVariables) {
        if (ToolBox.PREDEFINED.isLand(currentCondition.getRootSymbol())) {
            for (final TRSTerm argument : currentCondition.getArguments()) {
                assert argument instanceof TRSFunctionApplication;
                this.collectUsefulConstraints((TRSFunctionApplication) argument,
                    predecVariables);
            }
        } else {
            if (predecVariables.containsAll(currentCondition.getVariables())) {
                this.usefulConstraints.add(currentCondition);
                this.usefulVariables.addAll(currentCondition.getVariables());
            }
        }
    }
}
