package aprove.verification.idpframework.Processors.ItpfRules.poly;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class PolyRuleArithmeticToPoly extends ContextFreeItpfReplaceRule {

    final boolean onlyPolyTerms;

    public PolyRuleArithmeticToPoly(final boolean onlyPolyTerms) {
        super(new ExportableString("ItpfArithmeticToPoly"),
            new ExportableString("ItpfArithmeticToPoly"));
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

    @SuppressWarnings("unchecked")
    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive, final ImplicationType executionRequirements,
        final ApplicationMode mode, final Abortion aborter) {
        if (atom.isItp()) {
            final ItpfItp itp = (ItpfItp) atom;

            if (itp.getRelation() == ItpRelation.TO_TRANS || itp.getRelation() == ItpRelation.TO_PLUS && this.isDefinedLeft(idp, itp.getL())) {
                final boolean isPolynomialLeft = PredefinedUtil.isPolynomialTerm(itp.getL());

                if ((this.onlyPolyTerms || executionRequirements.isComplete()) && !isPolynomialLeft) {
                    return null;
                }

                boolean onlyArithmeticLeft = true;

                if (!isPolynomialLeft) {
                    final Set<IFunctionSymbol<?>> leftFunctionSymbols =
                        itp.getL().getFunctionSymbols();

                    final ImmutableSet<IFunctionSymbol<?>> definedSymbols =
                        idp.getIdpGraph().getDefinedSymbols();

                    final Set<IVariable<?>> sVars = CollectionUtil.getVariables(s);

                    for (final IFunctionSymbol<?> fs : leftFunctionSymbols) {
                        if ((definedSymbols.contains(fs) || PredefinedUtil.isPredefined(fs))
                            && !PredefinedUtil.isArithemeticFunction(fs)
                            && !PredefinedUtil.isInt(fs, DomainFactory.INTEGERS)) {
                            onlyArithmeticLeft = false;
                            break;
                        }
                    }

                    if (onlyArithmeticLeft) {
                        for (final IVariable<?> var : itp.getL().getVariables()) {
                            if (!var.getDomain().isIntegerDomain()
                                || !sVars.contains(var)) {
                                onlyArithmeticLeft = false;
                                break;
                            }
                        }
                    }
                }

                boolean integerNormalRight;
                if (itp.getR().isVariable()) {
                    final IVariable<?> rightVar = (IVariable<?>) itp.getR();
                    integerNormalRight = rightVar.getDomain().isIntegerDomain();
                } else {
                    final IFunctionApplication<?> faR =
                        (IFunctionApplication<?>) itp.getR();
                    final IFunctionSymbol<?> rightRoot = faR.getRootSymbol();
                    if (rightRoot.getResultDomain().isIntegerDomain()) {
                        integerNormalRight =
                            PredefinedUtil.isInt((IFunctionSymbol<? extends IntegerDomain<?>>) rightRoot,
                                (IntegerDomain<?>) rightRoot.getResultDomain());
                    } else {
                        integerNormalRight = false;
                    }
                }

                if (onlyArithmeticLeft && integerNormalRight) {
                    final ItpfPolyAtom<?> polyAtom =
                        this.convertItp(itp.getL(), ConstraintType.EQ, itp.getR(),
                            idp.getIdpGraph().getPolyInterpretation());

                    final LiteralMap map = new LiteralMap();

                    if (!isPolynomialLeft) {
                        map.put(atom, positive);
                    }

                    map.put(polyAtom, true);

                    return this.createReplaceData(idp.getItpfFactory(), ItpfFactory.EMPTY_QUANTORS, map, isPolynomialLeft ? ImplicationType.EQUIVALENT : ImplicationType.COMPLETE, ApplicationMode.SingleStep, false);
                }
            }
        }
        return null;
    }

    private boolean isDefinedLeft(final IDPProblem idp, final ITerm<?> l) {
        final IDependencyGraph idpGraph = idp.getIdpGraph();
        for (final IFunctionSymbol<?> fs : l.getFunctionSymbols()) {
            if (!idpGraph.isConstructor(fs)) {
                return true;
            }
        }
        return false;
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
        final PolyRuleArithmeticToPoly other = (PolyRuleArithmeticToPoly) obj;
        if (this.onlyPolyTerms != other.onlyPolyTerms) {
            return false;
        }
        return true;
    }


}
