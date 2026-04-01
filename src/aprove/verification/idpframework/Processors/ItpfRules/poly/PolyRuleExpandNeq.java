package aprove.verification.idpframework.Processors.ItpfRules.poly;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.ItpfRules.ItpfAtomReplaceData.*;
import immutables.*;

/**
 * @author MP
 */
public class PolyRuleExpandNeq extends
    ContextFreeItpfReplaceRule {

    public PolyRuleExpandNeq() {
        super(new ExportableString("[P] ExpandNeq"),
            new ExportableString("[P] ExpandNeq"));
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
    public Collection<? extends Mark<?>> getUsedMarks() {
        return Collections.<Mark<?>> singleton(this);
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        if (atom.isPoly()) {
            return this.processLiteralTyped((ItpfPolyAtom<?>) atom, positive, executionRequirements, mode);
        } else {
            return null;
        }
    }

    private <C extends SemiRing<C>> ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteralTyped(
        final ItpfPolyAtom<C> atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode) {
        if (!positive) {
            final ItpfPolyAtom<C> polyAtom = atom;

            if (polyAtom.getConstraintType() == ConstraintType.EQ) {
                final PolyInterpretation<C> polyInterpretation = atom.getInterpretation();
                final ItpfFactory itpfFactory = polyInterpretation.getConstraintFactory();

                final ItpfPolyAtom<C> gtAtom = itpfFactory.createPoly(polyAtom.getPoly(), ConstraintType.GT, polyInterpretation);
                final ItpfPolyAtom<C> ltAtom = itpfFactory.createPoly(polyAtom.getPoly().negate(), ConstraintType.GT, polyInterpretation);

                final Collection<ItpfAtomReplaceData> replaceData = new ArrayList<ItpfAtomReplaceData>();
                replaceData.add(
                    new LiteralMapData(
                        new LiteralMap(gtAtom, true),
                        ITerm.EMPTY_SET));
                replaceData.add(
                    new LiteralMapData(
                        new LiteralMap(ltAtom, true),
                        ITerm.EMPTY_SET));

                return this.createReplaceData(ItpfFactory.EMPTY_QUANTORS, ImmutableCreator.create(replaceData), ImplicationType.EQUIVALENT, ApplicationMode.SingleStep, false);
            }
        }
        return null;
    }

}
