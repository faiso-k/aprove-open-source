package aprove.verification.idpframework.Processors.ItpfRules.poly;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Algorithms.UsableRules.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;

/**
 * @author Martin Pluecker
 */
public class PolyRuleReachabilityToPoly extends ContextFreeItpfReplaceRule {

    public PolyRuleReachabilityToPoly() {
        super(new ExportableString("[P] ReachabilityToPoly"),
            new ExportableString("[P] ReachabilityToPoly"));
    }

    @Override
    public boolean isApplicable(final IDPProblem idp) {
        return idp.getIdpGraph().getPolyInterpretation() != null;
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
        return this.equals(mark);
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive, final ImplicationType executionRequirements,
        final ApplicationMode mode, final Abortion aborter) {
        if (atom.isItp() && !executionRequirements.isComplete()) {
            final ItpfItp itp = (ItpfItp) atom;

            if (itp.getRelation().isRewriteRel()) {

                final ItpfFactory itpfFactory = idp.getItpfFactory();

                final ItpfTermUra uraAtom = itpfFactory.createTermUra(null, itp.getKLeft(), IActiveCondition.create(itp.getContextL()), itp.getL(), ItpRelation.ABSTRACT_GE);

                final ItpfPolyAtom<?> polyAtom =
                    this.convertItp(itp.getL(), ConstraintType.GE, itp.getR(),
                        idp.getIdpGraph().getPolyInterpretation());

                final ItpfImplication implication = itpfFactory.createImplication(
                    itpfFactory.create(uraAtom, true, ITerm.EMPTY_SET),
                    itpfFactory.create(polyAtom, true, ITerm.EMPTY_SET));

                final LiteralMap map = new LiteralMap();

                map.put(implication, true);

                return this.createReplaceData(itpfFactory, ItpfFactory.EMPTY_QUANTORS, map, ImplicationType.SOUND, ApplicationMode.SingleStep, false);
            }
        }
        return null;
    }

    private <C extends SemiRing<C>> ItpfPolyAtom<C> convertItp(final ITerm<?> left,
        final ConstraintType ct,
        final ITerm<?> right,
        final PolyInterpretation<C> interpretation) {

        final Polynomial<C> polyL =
            interpretation.interpretTerm(left, RelDependency.Increasing);

        final Polynomial<C> polyR =
            interpretation.interpretTerm(right, RelDependency.Increasing);

        final Polynomial<C> poly = polyL.subtract(polyR);

        final ItpfPolyAtom<C> polyAtom =
            interpretation.getConstraintFactory().createPoly(poly, ct,
                interpretation);

        return polyAtom;
    }

    private ConstraintType getConstraintType(final PredefinedFunction<?, ?> func) {
        final ConstraintType ct;
        switch (func.getFunc()) {
        case Ge:
            ct = ConstraintType.GE;
            break;
        case Gt:
            ct = ConstraintType.GE;
            break;
        case Eq:
            ct = ConstraintType.GE;
            break;
        default:
            ct = null;
        }
        return ct;
    }

    @Override
    public int hashCode() {
        final int prime = 17;
        final int result = 2;
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final PolyRuleReachabilityToPoly other = (PolyRuleReachabilityToPoly) obj;
        return true;
    }


}
