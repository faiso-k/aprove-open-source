package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Algorithms.Unification.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author mpluecke
 */
public class ItpfUnify extends ContextFreeItpfReplaceRule {

    public ItpfUnify() {
        super(new ExportableString("ItpfUnify"), new ExportableString(
            "ItpfUnify"));
    }

    @Override
    public boolean isApplicable(final IDPProblem idp) {
        return true;
    }

    @Override
    public boolean isComplete() {
        return true;
    }

    @Override
    public boolean isSound() {
        return true;
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
        return CompatibleMarkClasses.I_UNIFY.isCompatible(mark);
    }

    @Override
    public boolean equals(final Object obj) {
        if (obj == this) {
            return true;
        }

        if (obj == null) {
            return false;
        }

        return obj.getClass() == this.getClass();
    }
    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> preProcessClause(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context, final ItpfAndWrapper precondition, final ItpfConjClause c,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException {

        if (mode != ApplicationMode.NoOp) {

            // instantiate
            final ISubstitution preconditionMgu = this.extractUnificationsFromPrecondition(
                context,
                precondition.getFormula(),
                idp.getPredefinedMap());

            final Set<ITerm<?>> addToS = new LinkedHashSet<ITerm<?>>();

            final Set<Pair<ITerm<?>, ITerm<?>>> unificationProblem = this.extractUnificationProblem(preconditionMgu);

            for (final Map.Entry<? extends ItpfAtom, Boolean> literal : c.getLiterals().entrySet()) {
                if (literal.getKey().isItp() && literal.getValue()) {
                    final ItpfItp itp = (ItpfItp) literal.getKey();
                    if (itp.getRelation() == ItpRelation.EQ) {
                        unificationProblem.add(new Pair<ITerm<?>, ITerm<?>>(itp.getL(), itp.getR()));

                        if (c.getS().contains(itp.getR())) {
                            addToS.add(itp.getL());
                        }

                        if (c.getS().contains(itp.getL())) {
                            addToS.add(itp.getR());
                        }
                    }
                }
            }

            final Unification unify = new Unification(unificationProblem, idp.getPredefinedMap());

            ISubstitution mgu = unify.getMgu();

            if (mgu != null) {
                mgu = this.normalizeMGU(precondition.getTotalQuantification(), mgu);
            } else {
                return  new ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>(
                        new QuantifiedDisjunction<ItpfConjClause>(),
                        ImplicationType.EQUIVALENT,
                        ApplicationMode.SingleStep,
                        true);
            }

            if (!mgu.isEmpty() || !addToS.isEmpty()) {
                final ItpfFactory itpfFactory = idp.getItpfFactory();

                final PolyTermSubstitution sigma =
                    TermToPolyTermSubstitution.create(mgu, idp.getIdpGraph().getPredefinedMap(), idp.getIdpGraph().getPolyInterpretation());

                final LiteralMap substNewChildren = new LiteralMap();
                boolean changed = false;

                for (final Map.Entry<? extends ItpfAtom, Boolean> literal : c.getLiterals().entrySet()) {
                    final ItpfAtom oldAtom = literal.getKey();

                    if (!oldAtom.isImplication()) {
                        final ItpfAtom newAtom = oldAtom.applySubstitution(sigma);
                        if (newAtom != oldAtom) {
                            changed = true;
                        }
                        substNewChildren.put(newAtom, literal.getValue());
                    } else {
                        substNewChildren.put(oldAtom, literal.getValue());
                    }
                }

                final LinkedHashSet<ITerm<?>> newS =
                    new LinkedHashSet<ITerm<?>>(c.getS().size() + addToS.size());

                for (final ITerm<?> sTerm : c.getS()) {
                    final ITerm<?> newSTerm = sTerm.applySubstitution(sigma);
                    changed = changed || !newSTerm.equals(sTerm);
                    newSTerm.collectSubTerms(newS, false);
                }

                for (final ITerm<?> sTerm : addToS) {
                    final int newSSize = newS.size();
                    sTerm.collectSubTerms(newS, false);
                    final ITerm<?> newSTerm = sTerm.applySubstitution(sigma);
                    newSTerm.collectSubTerms(newS, false);
                    changed = changed || newSSize != newS.size();
                }

                final LinkedHashMap<IVariable<?>, ITerm<?>> localMgu = new LinkedHashMap<IVariable<?>, ITerm<?>>(mgu.getMap());
                localMgu.entrySet().removeAll(preconditionMgu.getMap().entrySet());
                for (final Map.Entry<IVariable<?>, ITerm<?>> localMguEntry : localMgu.entrySet()) {
                    if (!ItpfUtil.isQuantified(precondition.getTotalQuantification(), localMguEntry.getKey())) {
                        final ItpfItp itp = itpfFactory.createItp(localMguEntry.getKey(), null, null, ItpRelation.EQ, localMguEntry.getValue(), null, null);
                        changed = changed || !Boolean.TRUE.equals(c.getLiterals().get(itp));
                        substNewChildren.put(itp, Boolean.TRUE);
                    } else {
                        changed = true;
                    }
                }

                if (changed) {
                    return new ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>(
                            new QuantifiedDisjunction<ItpfConjClause>(
                                idp.getIdpGraph().getItpfFactory().createClause(
                                ImmutableCreator.create(substNewChildren),
                                ImmutableCreator.create(newS))),
                            ImplicationType.EQUIVALENT, ApplicationMode.SingleStep, true);
                }
            }
        }

        return new ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>(
                new QuantifiedDisjunction<ItpfConjClause>(c),
                ImplicationType.EQUIVALENT, ApplicationMode.NoOp, mode != ApplicationMode.NoOp);
    }

    private Set<Pair<ITerm<?>, ITerm<?>>> extractUnificationProblem(final ISubstitution mgu) {
        final Set<Pair<ITerm<?>, ITerm<?>>> unificationProblem = new LinkedHashSet<Pair<ITerm<?>,ITerm<?>>>();
        for (final Map.Entry<IVariable<?>, ? extends ITerm<?>> mguEntry : mgu.getMap().entrySet()) {
            unificationProblem.add(new Pair<ITerm<?>, ITerm<?>>(
                    mguEntry.getKey(),
                    mguEntry.getValue()));
        }

        return unificationProblem;
    }

    private ISubstitution extractUnificationsFromPrecondition(final ReplaceContext.ReplaceContextSkeleton context,
        final Itpf precondition,
        final IDPPredefinedMap predefinedMap) {
        if (!precondition.getClauses().isEmpty() && ! precondition.isTrue()) {
            final Iterator<ItpfConjClause> preconditionClauseIterator = precondition.getClauses().iterator();

            final ISubstitution firstClauseMgu = this.extractUnificationFromClause(
                precondition.getQuantification(),
                Collections.<Pair<ITerm<?>, ITerm<?>>>emptySet(),
                preconditionClauseIterator.next(),
                predefinedMap);

            if (firstClauseMgu == null) {
                return null;
            }

            final Map<IVariable<?>, ITerm<?>> res = new LinkedHashMap<IVariable<?>, ITerm<?>>(firstClauseMgu.getMap());

            while (preconditionClauseIterator.hasNext()) {
                final ISubstitution clauseMGU = this.extractUnificationFromClause(
                    precondition.getQuantification(),
                    Collections.<Pair<ITerm<?>, ITerm<?>>>emptySet(),
                    preconditionClauseIterator.next(),
                    predefinedMap);

                if (clauseMGU == null) {
                    return null;
                }

                res.entrySet().retainAll(
                    clauseMGU.getMap().entrySet());
            }

            return ISubstitution.create(ImmutableCreator.create(res), true);
        } else {
            return ISubstitution.emptySubstitution();
        }
    }

    private ISubstitution extractUnificationFromClause(final ImmutableList<ItpfQuantor> quantification,
        final Set<Pair<ITerm<?>, ITerm<?>>> preconditionUnificationProblem,
        final ItpfConjClause clause,
        final IDPPredefinedMap predefinedMap) {
        final Set<Pair<ITerm<?>, ITerm<?>>> unificationProblem = new LinkedHashSet<Pair<ITerm<?>, ITerm<?>>>(preconditionUnificationProblem);

        for (final Map.Entry<? extends ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
            if (literal.getKey().isItp() && literal.getValue()) {
                final ItpfItp itp = (ItpfItp) literal.getKey();
                if (itp.getRelation() == ItpRelation.EQ) {
                    unificationProblem.add(new Pair<ITerm<?>, ITerm<?>>(
                        itp.getL(), itp.getR()));
                }
            }
        }

        final Unification unify = new Unification(unificationProblem, predefinedMap);

        final ISubstitution mgu = unify.getMgu();

        if (mgu != null) {
            return this.normalizeMGU(quantification, mgu);
        } else {
            return null;
        }
    }

    private ISubstitution normalizeMGU(final ImmutableList<ItpfQuantor> quantification,
        final ISubstitution subst) {
        final Map<IVariable<?>, IVariable<?>> varRenaming = new LinkedHashMap<IVariable<?>, IVariable<?>>();
        for (final Map.Entry<IVariable<?>, ? extends ITerm<?>> entry : subst.getMap().entrySet()) {
            final IVariable<?> lVar = entry.getKey();
            final boolean lQuantified = ItpfUtil.isQuantified(quantification, lVar);

            final IVariable<?> rVar;
            boolean rQuantified;
            if (entry.getValue().isVariable()) {
                rVar = (IVariable<?>) entry.getValue();
                rQuantified = ItpfUtil.isQuantified(quantification, rVar);
            } else {
                rVar = null;
                rQuantified = false;
            }

            if (lQuantified) {
                if (rQuantified) {
                    if (lVar.compareTo(rVar) > 0) {
                        varRenaming.put(rVar, lVar);
                    }
                }
            } else {
                if (rQuantified) {
                    varRenaming.put(rVar, lVar);
                } else if (rVar != null) {
                    if (lVar.compareTo(rVar) > 0) {
                        varRenaming.put(rVar, lVar);
                    }
                }
            }
        }

        return subst.termCompose(VarRenaming.create(ImmutableCreator.create(varRenaming), true, null));
    }

    @Override
    protected ExecutionResult<? extends QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final aprove.verification.idpframework.Processors.ItpfRules.ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException {
        return null;
    }

}
