package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class ItpfRuleDropFreeVariables extends IDPExportable.IDPExportableSkeleton implements GenericItpfRule<Unused> {

    private final boolean hardMode;

    public ItpfRuleDropFreeVariables(final boolean hardMode) {
        this.hardMode = hardMode;
    }

    @Override
    public boolean isSound() {
        return true;
    }

    @Override
    public boolean isComplete() {
        return true;
    }

    @Override
    public boolean isApplicable(final IDPProblem idp) {
        return true;
    }

    @Override
    public boolean isApplicable(final IDPProblem idp,
        final Itpf formula,
        final ApplicationMode mode) {
        return this.isApplicable(idp);
    }

    @Override
    public boolean isAtomicMark() {
        return false;
    }

    @Override
    public boolean isClauseMark() {
        return false;
    }

    @Override
    public boolean isContextFree() {
        return true;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return this.equals(mark);
    }

    @Override
    public Collection<? extends Mark<?>> getUsedMarks() {
        return Collections.<Mark<?>> singleton(this);
    }

    @Override
    public ExecutionResult<Conjunction<Itpf>, Itpf> process(final IDPProblem idp,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException {
        if (executionRequirements.isComplete()) {
            return new ExecutionResult<Conjunction<Itpf>, Itpf>(
                    new Conjunction<Itpf>(formula),
                    ImplicationType.EQUIVALENT,
                    ApplicationMode.NoOp,
                    true);
        }

        final ImmutableSet<IVariable<?>> boundVariables = formula.getBoundVariables();
        final ImmutableSet<IVariable<?>> freeVariables = formula.getFreeVariables();
        final ItpfFactory itpfFactory = idp.getItpfFactory();

        final LinkedHashSet<ItpfConjClause> newClauses = new LinkedHashSet<ItpfConjClause>();
        boolean changed = false;

        ApplicationMode usedApplications = ApplicationMode.NoOp;
        ApplicationMode remainingAplications = mode;
        boolean fixpointReached = true;

        for (final ItpfConjClause clause : formula.getClauses()) {
            final Set<IVariable<?>> filteredBoundVariables;
            if (this.hardMode) {
                filteredBoundVariables = boundVariables;
            } else {
                filteredBoundVariables = this.getFilteredBoundVariables(boundVariables, freeVariables,
                    clause, remainingAplications);
            }

            final ApplicationMode neededSteps = ApplicationMode.getMode(filteredBoundVariables.size());
            if (!filteredBoundVariables.isEmpty()) {
                if (remainingAplications.compareTo(neededSteps) >= 0) {
                    usedApplications = usedApplications.increaseBy(neededSteps);
                    remainingAplications = remainingAplications.decreaseBy(neededSteps);
                    newClauses.add(this.filterClause(itpfFactory, clause, filteredBoundVariables));
                    changed = true;
                } else {
                    fixpointReached = false;
                    newClauses.add(clause);
                }
            } else {
                newClauses.add(clause);
            }
        }

        if (changed) {
            final Itpf newFormula = itpfFactory.create(
                formula.getQuantification(),
                ImmutableCreator.create(newClauses));
            return new ExecutionResult<Conjunction<Itpf>, Itpf>(
                    new Conjunction<Itpf>(newFormula),
                    ImplicationType.SOUND,
                    usedApplications,
                    fixpointReached);
        } else {
            return new ExecutionResult<Conjunction<Itpf>, Itpf>(
                    new Conjunction<Itpf>(formula),
                    ImplicationType.EQUIVALENT,
                    usedApplications,
                    fixpointReached);
        }
    }

    private LinkedHashSet<IVariable<?>> getFilteredBoundVariables(final ImmutableSet<IVariable<?>> boundVariables,
        final ImmutableSet<IVariable<?>> freeVariables,
        final ItpfConjClause clause,
        final ApplicationMode remainingAplications) {
        final LinkedHashSet<IVariable<?>> filteredBoundVariables = new LinkedHashSet<IVariable<?>>();
        if (!remainingAplications.isNoOp()) {
            final EquivalenceClassMap<IVariable<?>> varEqClasses = new EquivalenceClassMap<IVariable<?>>();
            varEqClasses.addElements(clause.getVariables());
            this.processVarEqClasses(clause, varEqClasses);

            for (final IVariable<?> boundVariable : boundVariables) {

                final Set<IVariable<?>> boundVarEqClass = varEqClasses.getClass(boundVariable);
                boolean variableNeeded = boundVarEqClass == null;
                if (!variableNeeded) {
                    for (final IVariable<?> freeVariable : freeVariables) {
                        if (boundVarEqClass.contains(freeVariable)) {
                            variableNeeded = true;
                            break;
                        }
                    }
                }
                if (!variableNeeded) {
                    filteredBoundVariables.add(boundVariable);
                }
            }
        }
        return filteredBoundVariables;
    }

    private ItpfConjClause filterClause(final ItpfFactory itpfFactory,
        final ItpfConjClause clause,
        final Set<IVariable<?>> filteredBoundVariables) {
        final LiteralMap newLiterals = new LiteralMap();
        boolean changed = false;

        for (final Map.Entry<ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
            final ItpfAtom atom = literal.getKey();
            if (atom.isImplication()) {
                final ItpfImplication implication = (ItpfImplication) atom;
                final Itpf newPrecondition = this.filterFormula(itpfFactory, implication.getPrecondition(), filteredBoundVariables);
                final Itpf newConclusion = this.filterFormula(itpfFactory, implication.getConclusion(), filteredBoundVariables);
                if (newPrecondition != implication.getPrecondition() || newConclusion != implication.getConclusion()) {
                    newLiterals.put(itpfFactory.createImplication(newPrecondition, newConclusion),
                        literal.getValue());
                    changed = true;
                } else {
                    newLiterals.put(atom, literal.getValue());
                }
            } else {
                final Collection<IVariable<?>> atomVars = atom.getVariables();
                boolean filter = false;
                for (final IVariable<?> filteredVar : filteredBoundVariables) {
                    if (atomVars.contains(filteredVar)) {
                        filter = true;
                        break;
                    }
                }

                if (!filter) {
                    newLiterals.put(atom, literal.getValue());
                } else {
                    changed = true;
                }
            }
        }

        final Set<ITerm<?>> newS = new LinkedHashSet<ITerm<?>>();
        for (final ITerm<?> t : clause.getS()) {
            boolean filterTerm = false;
            for (final IVariable<?> v : t.getVariables()) {
                if (filteredBoundVariables.contains(v)) {
                    filterTerm = true;
                    break;
                }
            }
            if (filterTerm) {
                changed = true;
            } else {
                newS.add(t);
            }
        }

        if (changed) {
            return itpfFactory.createClause(
                ImmutableCreator.create(newLiterals),
                ImmutableCreator.create(newS));
        } else {
            return clause;
        }
    }

    private Itpf filterFormula(final ItpfFactory itpfFactory,
        final Itpf formula,
        final Set<IVariable<?>> filteredBoundVariables) {
        final Set<ItpfConjClause> newClauses = new LinkedHashSet<ItpfConjClause>();

        boolean changed = false;

        for (final ItpfConjClause clause : formula.getClauses()) {
            final ItpfConjClause newClause = this.filterClause(itpfFactory, clause, filteredBoundVariables);
            newClauses.add(newClause);
            changed = changed || newClause != clause;
        }

        if (changed) {
            return itpfFactory.create(ImmutableCreator.create(newClauses));
        } else {
            return formula;
        }
    }

    private void processVarEqClasses(final ItpfConjClause clause,
        final EquivalenceClassMap<IVariable<?>> varEqClasses) {
        for (final ItpfAtom atom : clause.getLiterals().keySet()) {
            if (atom.isImplication()) {
                final ItpfImplication implication = (ItpfImplication) atom;
                this.processVarEqClasses(implication.getPrecondition(), varEqClasses);
                this.processVarEqClasses(implication.getConclusion(), varEqClasses);
            } else {
                varEqClasses.mergeClasses(atom.getVariables());
            }
        }
    }

    private void processVarEqClasses(final Itpf formula,
        final EquivalenceClassMap<IVariable<?>> varEqClasses) {
        for (final ItpfConjClause clause : formula.getClauses()) {
            this.processVarEqClasses(clause, varEqClasses);
        }
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        sb.append(eu.escape("[i] DropFreeVariables"));
    }

}
