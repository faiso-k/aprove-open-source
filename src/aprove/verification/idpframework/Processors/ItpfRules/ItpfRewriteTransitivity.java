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
import immutables.*;

/**
 *
 * @author MP
 */
public class ItpfRewriteTransitivity extends
        ContextFreeItpfReplaceRule {

    public ItpfRewriteTransitivity() {
        super(new ExportableString("RewriteTransitivity"), new ExportableString("RewriteTransitivity"));
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
        return CompatibleMarkClasses.REWRITE_TRANSITIVITY.isCompatible(mark);
    }


    @Override
    protected final ExecutionResult<? extends QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processImplicationOrLiteral(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Map<ItpfAtom, Boolean> otherLiterals,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException {
        if (atom.isImplication()) {
            return super.processImplicationOrLiteral(idp, context, precondition, otherLiterals, s, atom, positive, executionRequirements, mode, aborter);
        } else if (atom.isItp() && positive) {
            final ItpfFactory itpfFactory = idp.getIdpGraph().getItpfFactory();

            // fast hack removing loops
            if (otherLiterals.size() > 50) {
                return null;
            }

            final LiteralMap otherPreconditionLiterals =
                new LiteralMap(otherLiterals);
            otherPreconditionLiterals.remove(atom);

            final ItpfConjClause otherPreconditionClause = itpfFactory.createClause(ImmutableCreator.create(otherPreconditionLiterals), ITerm.EMPTY_SET);


            final ItpfItp itp = (ItpfItp) atom;
            if (itp.getRelation().isRewriteRel() && itp.getRelation() != ItpRelation.TO_SYM_TRANS) {
                final LiteralMap possibleRewrites = new LiteralMap();

                IVariable<?> rVar;
                if (itp.getR().isVariable()) {
                    rVar = (IVariable<?>) itp.getR();
                } else {
                    rVar = null;
                }
                final boolean rGround = itp.getR().isGroundTerm();

                boolean mustAddOriginal = false;

                final ItpfAndWrapper totalPrecondition = precondition.addFormula(new QuantifiedDisjunction<ItpfConjClause>(otherPreconditionClause));
                for (final ItpfConjClause clause : totalPrecondition.getFormula().getClauses()) {
                    for (final Map.Entry<ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
                        if (literal.getKey().isItp()) {
                            final ItpfItp precondItp = (ItpfItp) literal.getKey();
                            if (precondItp.getRelation().isRewriteRel()) {
                                if (itp.canIgnoreContextL() && itp.canIgnoreContextR()) {
                                    // left transitivity
                                    final Set<IPosition> subPositions = itp.getL().getSubtermPositions(precondItp.getR());
                                    for (final IPosition subPosition : subPositions) {
                                        final ITerm<?> newL = itp.getL().replaceAt(subPosition, precondItp.getL());
                                        if (!newL.equals(itp.getL())) {
                                            final ItpfItp newItp = itpfFactory.createItp(newL, itp.getKLeft(), itp.getContextL(),
                                                ItpRelation.TO_TRANS,
                                                itp.getR(), itp.getKRight(), itp.getContextR());
                                            possibleRewrites.put(newItp, true);
                                        } else {
                                            mustAddOriginal = true;
                                        }
                                    }
                                } else if (rVar != null) {
                                    mustAddOriginal = mustAddOriginal || precondItp.getVariables().contains(rVar);
                                }
                                if (!rGround && precondItp.canIgnoreContextL() && precondItp.canIgnoreContextR()) {
                                    // right transitivity
                                    final Set<IPosition> subPositions = itp.getR().getSubtermPositions(precondItp.getL());
                                    for (final IPosition subPosition : subPositions) {
                                        final ITerm<?> newR = itp.getR().replaceAt(subPosition, precondItp.getR());
                                        if (!newR.equals(itp.getR())) {
                                            final ItpfItp newItp = itpfFactory.createItp(itp.getL(), itp.getKLeft(), itp.getContextL(),
                                                ItpRelation.TO_TRANS,
                                                newR, itp.getKRight(), itp.getContextR());
                                            possibleRewrites.put(newItp, true);
                                        } else {
                                            mustAddOriginal = true;
                                        }
                                    }
                                } else if (rVar != null) {
                                    mustAddOriginal = mustAddOriginal || precondItp.getVariables().contains(rVar);
                                }
                            }
                        }
                    }
                }

                if (!possibleRewrites.isEmpty()) {
                    ImplicationType implication;
                    if (executionRequirements.isComplete() || mustAddOriginal || rVar == null || !ItpfUtil.isQuantified(precondition.getTotalQuantification(), rVar)) {
                        possibleRewrites.put(itp, positive);
                        implication = ImplicationType.EQUIVALENT;
                    } else {
                        implication = ImplicationType.SOUND;
                    }

                    return this.createReplaceData(
                        itpfFactory,
                        ItpfFactory.EMPTY_QUANTORS,
                        possibleRewrites,
                        implication,
                        ApplicationMode.SingleStep,
                        true);
                }
            }
        }
        return null;
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
        throw new UnsupportedOperationException("unused method");
    }

}
