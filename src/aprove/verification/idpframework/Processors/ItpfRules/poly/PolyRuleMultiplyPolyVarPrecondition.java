package aprove.verification.idpframework.Processors.ItpfRules.poly;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class PolyRuleMultiplyPolyVarPrecondition extends AbstractItpfReplaceRule<ReplaceContext.ReplaceContextSkeleton, ItpfConjClause, Unused> {

    public PolyRuleMultiplyPolyVarPrecondition() {
        super(new ExportableString("PolyRuleMultiplyPolyVarPrecondition"), new ExportableString("PolyRuleMultiplyPolyVarPrecondition"));
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
        return true;
    }

    @Override
    public boolean isClauseMark() {
        return true;
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
    public Collection<Mark<Unused>> getUsedMarks() {
        return Collections.<Mark<Unused>> singleton(this);
    }

    @Override
    protected aprove.verification.idpframework.Processors.ItpfRules.ReplaceContext.ReplaceContextSkeleton createContext(final IDPProblem idp,
        final ItpfAndWrapper precondition,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        return new ReplaceContext.ReplaceContextSkeleton();
    }

    @Override
    protected ExecutionResult<? extends QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> processImplication(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfImplication implication,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException {

        final ItpfBoolPolyVar<?> boolPolyVarPrecondition =
            this.getBoolPolyVarPrecondition(implication);

        if (boolPolyVarPrecondition != null) {

            final ItpfFactory itpfFactory = idp.getItpfFactory();

            final Itpf multipliedConclusion = this.multiplyPolyFormula(itpfFactory, itpfFactory.getPolyFactory().create(boolPolyVarPrecondition.getPolyVar()), implication.getConclusion(), ImplicationType.EQUIVALENT);

            if (multipliedConclusion != null) {
                ApplicationMode remainingApplications = mode.decreaseOneStep();
                ApplicationMode usedApplications = ApplicationMode.SingleStep;

                final ExecutionResult<Conjunction<Itpf>, Itpf> processedConclusion =
                    this.process(idp, multipliedConclusion, executionRequirements, remainingApplications, aborter);

                remainingApplications = remainingApplications.decreaseBy(processedConclusion.usedApplications);
                usedApplications = usedApplications.increaseBy(processedConclusion.usedApplications);

                final ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> r =
                    new ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>(multipliedConclusion, processedConclusion.implication.mult(executionRequirements), usedApplications, processedConclusion.fixpointReached);

                return r;
            }
        }

        return super.processImplication(idp, context, precondition, s, implication, positive, executionRequirements, mode, aborter);
    }

    private <C extends SemiRing<C>> Itpf multiplyPolyFormula(final ItpfFactory itpfFactory,
        final Polynomial<C> boolPolyVarPrecondition,
        final Itpf formula, final ImplicationType executionRequirement) {
        if (formula.isTrue()) {
            return formula;
        } else if (formula.isFalse()) {
            return null;
        }

        final Set<ItpfConjClause> newClauses = new LinkedHashSet<ItpfConjClause>();

        boolean changed = false;
        for (final ItpfConjClause clause : formula.getClauses()) {
            final LiteralMap newListerals = new LiteralMap();

            boolean changedClause = false;

            for (final Map.Entry<? extends ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
                if (literal.getKey().isPoly()) {
                    @SuppressWarnings("unchecked")
                    final ItpfPolyAtom<C> polyAtom = (ItpfPolyAtom<C>) literal.getKey();

                    if (literal.getValue() && polyAtom.getConstraintType() == ConstraintType.GE) {
                        final Polynomial<C> newPoly = polyAtom.getPoly().mult(boolPolyVarPrecondition);
                        final ItpfPolyAtom<C> newPolyAtom = itpfFactory.createPoly(newPoly, polyAtom.getConstraintType(), polyAtom.getInterpretation());
                        newListerals.put(newPolyAtom, literal.getValue());
                        changedClause = true;
                    } else if (executionRequirement.isSound()) {
                        return null;
                    } else {
                        newListerals.put(literal.getKey(), literal.getValue());
                    }
                } else if (literal.getKey().isImplication() && literal.getValue()) {
                    final ItpfImplication implication = (ItpfImplication) literal.getKey();
                    final Itpf newPrecondition = this.multiplyPolyFormula(itpfFactory, boolPolyVarPrecondition, implication.getPrecondition(), executionRequirement.invert());
                    if (newPrecondition == null) {
                        return null;
                    }

                    final Itpf newConclusion = this.multiplyPolyFormula(itpfFactory, boolPolyVarPrecondition, implication.getConclusion(), executionRequirement);
                    if (newConclusion == null) {
                        return null;
                    }

                    if (newPrecondition != implication.getPrecondition() || newConclusion != implication.getConclusion()) {
                        final ItpfImplication newImplication = itpfFactory.createImplication(newPrecondition, newConclusion);
                        newListerals.put(newImplication, literal.getValue());
                        changedClause = true;
                    } else {
                        newListerals.put(literal.getKey(), literal.getValue());
                    }
                } else {
                    return null;
//                } else {
//                    newListerals.put(literal.getKey(), literal.getValue());
                }
            }

            if (changedClause) {
                newClauses.add(itpfFactory.createClause(ImmutableCreator.create(newListerals), clause.getS()));
                changed = true;
            } else {
                newClauses.add(clause);
            }
        }

        if (changed) {
            return itpfFactory.create(formula.getQuantification(), ImmutableCreator.create(newClauses));
        } else {
            return formula;
        }
    }

    private ItpfBoolPolyVar<?> getBoolPolyVarPrecondition(final ItpfImplication implication) {
        ItpfBoolPolyVar<?> boolPolyVarPrecondition = null;
        if (implication.getPrecondition().getClauses().size() == 1) {
            final ItpfConjClause clause = implication.getPrecondition().getClauses().iterator().next();
            if (clause.getLiterals().size() == 1) {
                final Map.Entry<? extends ItpfAtom, Boolean> literal = clause.getLiterals().entrySet().iterator().next();
                if (literal.getKey().isBoolPolyVar() && literal.getValue().booleanValue()) {
                    boolPolyVarPrecondition = (ItpfBoolPolyVar<?>) literal.getKey();
                }
            }
        }
        return boolPolyVarPrecondition;
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> processLiteral(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        return null;
    }

    @Override
    protected ItpfConjClause createReplaceData(final ItpfFactory itpfFactory,
        final LiteralMap conjunction, final ImmutableSet<ITerm<?>> sTerms) {
        return itpfFactory.createClause(ImmutableCreator.create(conjunction), ITerm.EMPTY_SET);
    }

}
