package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.ItpfRules.RuleExtractPrecondition.*;
import immutables.*;

/**
 *
 * @author MP
 */

/**
 * extracts a precondtiton Phi => Psi is transformed to a => Psi & Phi => a
 */
public class RuleExtractPrecondition extends AbstractItpfReplaceRule.ItpfReplaceRuleSkeleton<SideConstraintContext, Unused> {

    public RuleExtractPrecondition() {
        super(new ExportableString("RuleExtractPrecondition"), new ExportableString("RuleExtractPrecondition"));
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
        return idp.getIdpGraph().getPolyInterpretation() != null;
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
        return false;
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
    protected SideConstraintContext createContext(final IDPProblem idp,
        final ItpfAndWrapper precondition,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        return new SideConstraintContext();
    }

    @Override
    protected ExecutionResult<Conjunction<Itpf>, Itpf> postProcess(final IDPProblem idp,
        final SideConstraintContext context,
        final ItpfAndWrapper precondition,
        final ExecutionResult<Conjunction<Itpf>, Itpf> result,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        if (!context.isEmpty()) {
            final LinkedHashSet<Itpf> totalContraints = new LinkedHashSet<Itpf>(context.getConstraints());
            totalContraints.addAll(result.asCollection());

            return new ExecutionResult<Conjunction<Itpf>, Itpf>(
                new Conjunction<Itpf>(ImmutableCreator.create(totalContraints)),
                result.implication, result.usedApplications, result.fixpointReached);
        } else {
            return result;
        }
    }

    @Override
    protected ExecutionResult<? extends QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processImplication(final IDPProblem idp,
        final SideConstraintContext context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfImplication implication,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException {
        boolean fixpointReached = true;
        if (!mode.isNoOp() && !executionRequirements.isComplete()) {

            boolean mustExtractPrecondition = !implication.getPrecondition().isFalse() && !implication.getPrecondition().isFalse();
            if (mustExtractPrecondition && implication.getPrecondition().getClauses().size() == 1) {
                final ItpfConjClause clause = implication.getPrecondition().getClauses().iterator().next();
                if (clause.getLiterals().size() == 1) {
                    final Map.Entry<? extends ItpfAtom, Boolean> literal = clause.getLiterals().entrySet().iterator().next();
                    if (literal.getKey().isBoolPolyVar() && literal.getValue().booleanValue()) {
                        mustExtractPrecondition = false;
                    }
                }
            }

            if (mustExtractPrecondition) {
                final ItpfFactory itpfFactory = idp.getItpfFactory();

                final PolyInterpretation<?> polyInterpretation = idp.getPolyInterpretation();

                final ItpfBoolPolyVar<?> boolPolyVar =
                    this.createBoolPolyVar(polyInterpretation);

                final Itpf preconditionVar = itpfFactory.create(boolPolyVar, true, ITerm.EMPTY_SET);

                final ItpfImplication newImplication = itpfFactory.createImplication(preconditionVar, implication.getConclusion());

                ApplicationMode remainingApplications = mode.decreaseOneStep();
                ApplicationMode usedApplications = ApplicationMode.SingleStep;

                final ExecutionResult<? extends QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> result =
                    super.processImplication(idp, context, precondition, s, newImplication, positive, executionRequirements, remainingApplications, aborter);

                remainingApplications = remainingApplications.decreaseBy(result.usedApplications);
                usedApplications = usedApplications.increaseBy(result.usedApplications);
                fixpointReached = fixpointReached && result.fixpointReached;

                // add new side constraint
                final ItpfImplication sideConstraintImplication = itpfFactory.createImplication(
                    itpfFactory.createAnd(preconditionVar, itpfFactory.createQuantorFree(precondition.getFormula())),
                    implication.getPrecondition());

                final Itpf sideConstraint = itpfFactory.create(
                    precondition.getTotalQuantification(),
                    itpfFactory.createClause(sideConstraintImplication,
                        true,
                        ITerm.EMPTY_SET));

                final ExecutionResult<Conjunction<Itpf>, Itpf> processedSideConstraint =
                    this.process(idp, sideConstraint, ImplicationType.COMPLETE, remainingApplications, aborter);

                fixpointReached = fixpointReached && processedSideConstraint.fixpointReached;

                remainingApplications = remainingApplications.decreaseBy(processedSideConstraint.usedApplications);
                usedApplications = usedApplications.increaseBy(processedSideConstraint.usedApplications);

                context.addAll(processedSideConstraint.asCollection());

                return result.multImplication(ImplicationType.SOUND).setUsedApplications(usedApplications, fixpointReached);
            }
        }

        return super.processImplication(idp, context, precondition, s, implication, positive, executionRequirements, mode, aborter);
    }


    private <C extends SemiRing<C>> ItpfBoolPolyVar<C> createBoolPolyVar(final PolyInterpretation<C> polyInterpretation) {
        final ItpfBoolPolyVar<C> boolPolyVar = polyInterpretation.getConstraintFactory().createBoolPolyVar(polyInterpretation.getNextBoolCoeff(), polyInterpretation);
        return boolPolyVar;
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final SideConstraintContext context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        return null;
    }

    public static class SideConstraintContext extends ReplaceContext.ReplaceContextSkeleton implements Iterable<Itpf> {

        private final LinkedHashSet<Itpf> constraints;

        public SideConstraintContext() {
            this.constraints = new LinkedHashSet<Itpf>();
        }

        public void addAll(final ImmutableCollection<Itpf> constraints) {
            this.constraints.addAll(constraints);
        }

        public boolean isEmpty() {
            return this.constraints.isEmpty();
        }

        @Override
        public Iterator<Itpf> iterator() {
            return this.constraints.iterator();
        }

        public LinkedHashSet<Itpf> getConstraints() {
            return this.constraints;
        }


    }

}
