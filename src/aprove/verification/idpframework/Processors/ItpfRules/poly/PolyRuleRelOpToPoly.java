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
public class PolyRuleRelOpToPoly extends ContextFreeItpfReplaceRule {

    final boolean onlyPolyTerms;

    public PolyRuleRelOpToPoly(final boolean onlyPolyTerms) {
        super(new ExportableString("PolyRuleRelOpToPoly"), new ExportableString(
            "PolyRuleRelOpToPoly"));
        this.onlyPolyTerms = onlyPolyTerms;
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
        return this.onlyPolyTerms;
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
    protected ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive, final ImplicationType executionRequirements,
        final ApplicationMode mode, final Abortion aborter){
        if (atom.isItp()) {
            final ItpfItp itp = (ItpfItp) atom;

            if (itp.canIgnoreContextL() && !itp.getL().isVariable()) {
                final IFunctionApplication<?> faL =
                    (IFunctionApplication<?>) itp.getL();
                final PredefinedSemantics<?> sem =
                    faL.getRootSymbol().getSemantics();

                if (sem != null && !sem.isConstructor()) {
                    final PredefinedFunction<?, ?> func =
                        (PredefinedFunction<?, ?>) sem;
                    final ConstraintType ct = this.getConstraintType(func);

                    if (ct != null) {

                        Boolean polyPositive = null;

                        if (IDPPredefinedMap.isBooleanTrue(itp.getR())) {
                            polyPositive = true;
                        } else if (IDPPredefinedMap.isBooleanFalse(itp.getR())) {
                            polyPositive = false;
                        }

                        if (polyPositive != null) {
                            if (!positive) {
                                polyPositive = !polyPositive;
                            }

                            final boolean isPolyTerm = PredefinedUtil.isPolynomialTerm(faL.getArgument(0)) && PredefinedUtil.isPolynomialTerm(faL.getArgument(1));

                            if ((this.onlyPolyTerms || executionRequirements.isSound()) && !isPolyTerm) {
                                return null;
                            }

                            final ItpfFactory itpfFactory = idp.getItpfFactory();

                            final ItpfAtom polyAtom =
                                this.convertItp(faL.getArgument(0), ct,
                                    faL.getArgument(1),
                                    idp.getIdpGraph().getPolyInterpretation());

                            final LiteralMap map = new LiteralMap();

                            if (!isPolyTerm) {
                                map.put(atom, positive);

                                final ItpfTermUra uraAtomLeft = itpfFactory.createTermUra(null, itp.getKLeft(), IActiveCondition.create(itp.getContextL()), itp.getL(), ItpRelation.ABSTRACT_GE);
                                final ItpfTermUra uraAtomRight = itpfFactory.createTermUra(null, RelDependency.Decreasing.combine(itp.getKRight()), IActiveCondition.create(itp.getContextR()), itp.getR(), ItpRelation.ABSTRACT_GE);

                                map.put(uraAtomLeft, positive);
                                map.put(uraAtomRight, positive);

                            } else {
                                map.put(polyAtom, polyPositive);
                            }

                            return this.createReplaceData(itpfFactory, ItpfFactory.EMPTY_QUANTORS, map, isPolyTerm ? ImplicationType.EQUIVALENT : ImplicationType.COMPLETE, ApplicationMode.SingleStep, false);
                        }
                    }
                }
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
            ct = ConstraintType.GT;
            break;
        case Eq:
            ct = ConstraintType.EQ;
            break;
        default:
            ct = null;
        }
        return ct;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return this.equals(mark);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (this.onlyPolyTerms ? 1231 : 1237);
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
        final PolyRuleRelOpToPoly other = (PolyRuleRelOpToPoly) obj;
        if (this.onlyPolyTerms != other.onlyPolyTerms) {
            return false;
        }
        return true;
    }



}
