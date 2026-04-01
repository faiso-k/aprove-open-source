package aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class IDPRuleApplication<FormulaType extends ProcessableFormula, RuleType extends ExecutableRule<FormulaType, ?>>
        implements IDPSchedulerStrategy<FormulaType, RuleType> {

    private final RuleType rule;
    private final ApplicationMode mode;

    public IDPRuleApplication(final RuleType rule) {
        this(rule, ApplicationMode.Multistep);
    }

    public IDPRuleApplication(final RuleType rule, final ApplicationMode mode) {
        this.rule = rule;
        this.mode = mode;
    }

    @Override
    public Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>> apply(final ItpfSchedulerProof<FormulaType, RuleType> proof,
        final ImplicationType executionRequirements,
        final Abortion aborter) throws AbortionException {
        final IDPProblem idp = proof.getIDP();
        final IDependencyGraph graph = idp.getIdpGraph();
        boolean successfull = false;

        if (this.rule.isApplicable(idp) && this.mode != ApplicationMode.NoOp) {
            final PolyInterpretation<?> polyInterpretation =
                idp.getIdpGraph().getPolyInterpretation();

            for (final FormulaType formulaToProcess : proof.getLastFormulaStates()) {
                if (this.rule.isApplicable(idp, formulaToProcess, this.mode)) {
                    final ExecutionResult<Conjunction<FormulaType>, FormulaType> newFormulas =
                        this.rule.process(proof.getIDP(), formulaToProcess, executionRequirements, this.mode,
                            aborter);

                    if (!newFormulas.result.isSingleton(formulaToProcess)) {
                        for (final FormulaType newFormula : newFormulas.result) {
                            if (newFormula != formulaToProcess) {
                                if (Globals.useAssertions) {
                                    // see definition if ITPF-rule
                                    final Set<IVariable<?>> newFreeVars =
                                        new LinkedHashSet<IVariable<?>>(
                                            newFormula.getFreeVariables());
                                    newFreeVars.removeAll(formulaToProcess.getFreeVariables());

                                    final Set<ImmutablePair<INode, ImmutableTermSubstitution>> formulaNodes =
                                        formulaToProcess.getNodes();

                                    for (final ImmutablePair<INode, ImmutableTermSubstitution> nodeWithSubst : formulaNodes) {
                                        newFreeVars.removeAll(graph.getTerm(nodeWithSubst.x).applySubstitution(nodeWithSubst.y).getVariables());
                                        if (newFreeVars.isEmpty()) {
                                            break;
                                        }
                                    }

                                    final Iterator<IVariable<?>> newFreeVarsIterator =
                                        newFreeVars.iterator();

                                    final SideConstraintStore sideConstraints =
                                        graph.getSideConstraints();


                                    while (newFreeVarsIterator.hasNext()) {
                                        final IVariable<?> var =
                                            newFreeVarsIterator.next();
                                        if (sideConstraints.isReplacement(var)) {
                                            newFreeVarsIterator.remove();
                                        } else if (var instanceof IVariable<?>) {
                                            if (polyInterpretation.isExistQuantified(var) || polyInterpretation.getVariableInterpretations().values().contains(var)) {
                                                newFreeVarsIterator.remove();
                                            }
                                        }
                                    }

                                    assert newFreeVars.isEmpty() : this.rule + " introduced free variables: "
                                        + newFreeVars;
                                }
                            }
                        }
                        if (proof.addStep(formulaToProcess, this.rule, newFormulas.implication, newFormulas.result)) {
                            successfull = true;
                        }
                    }
                    aborter.checkAbortion();
                }
            }

        }

        return new Pair<Boolean, IDPSchedulerStrategy<FormulaType, RuleType>>(
            successfull, null);
    }

    @Override
    public Set<RuleType> getAllRules() {
        return Collections.singleton(this.rule);
    }

    @Override
    public String toString() {
        return "IDPRuleApplication " + this.rule + " @ " + this.mode;
    }

}
