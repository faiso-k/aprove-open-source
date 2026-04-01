package aprove.verification.idpframework.Processors.NonInf.ItpfRules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class PolyRuleSolveBoundConstraints extends ContextFreeItpfReplaceRule {

    public PolyRuleSolveBoundConstraints() {
        super(new ExportableString("[P] SolveBoundConstraints"), new ExportableString("[P] SolveBoundConstraints"));
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
        return mark.getClass().equals(this.getClass());
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive, final ImplicationType executionRequirements,
        final ApplicationMode mode, final Abortion aborter) {
        if (atom.isPoly()) {
            return this.processPolyAtom(atom, positive, idp.getIdpGraph().getPolyInterpretation());
        }
        return null;
    }

    private <C extends SemiRing<C>> ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processPolyAtom(final ItpfAtom atom,
        final Boolean positive,
        final PolyInterpretation<C> polyInterpretation) {

        @SuppressWarnings("unchecked")
        final ItpfPolyAtom<C> polyAtom = (ItpfPolyAtom<C>) atom;
        if (polyAtom.getConstraintType() == ConstraintType.EQ) {
            return null;
        }

        final Polynomial<C> poly = polyAtom.getPoly();
        final PolyFactory polyFactory = polyInterpretation.getFactory();
        final ItpfFactory itpfFactory = polyInterpretation.getConstraintFactory();
        final IVariable<C> boundConstant = polyInterpretation.getBoundConstant();
        final C ring = poly.getRing();

        boolean foundBound = false;
        final LiteralMap newConstraints = new LiteralMap();

        Polynomial<C> boundCoeffSum = polyFactory.zero(ring);
        boolean hasBoundCoeffGtZero = false;
        boolean hasNonBoundMonomials = false;

        for (final Map.Entry<Monomial<C>, C> monomialEntry : poly.getMonomials().entrySet()) {
            final ImmutableSet<? extends IVariable<C>> variables = monomialEntry.getKey().getVariables();
            if (variables.contains(boundConstant)) {
                boolean boundNeg = false;
                for (final Map.Entry<? extends PolyVariable<C>, BigInt> varExponent : monomialEntry.getKey().getExponents().entrySet()) {
                    if (varExponent.getKey().equals(boundConstant)) {
                        boundNeg = !varExponent.getValue().isEven();
                    }
                }

                foundBound = true;

                if (variables.size() == 1) {
                    final Integer signum = monomialEntry.getValue().signum();

                    if (boundNeg == signum < 0) {
                        hasBoundCoeffGtZero = true;
                        continue;
                    } else {
                        return null;
                    }
                }

                // remaining poly must be < 0 iff boundNeg
                final LinkedHashMap<PolyVariable<C>, BigInt> newConstraintMonomial =
                    new LinkedHashMap<PolyVariable<C>, BigInt>(monomialEntry.getKey().getExponents());
                newConstraintMonomial.remove(boundConstant);

                Polynomial<C> remainingPoly = polyFactory.create(polyFactory.createMonomial(ring, ImmutableCreator.create(newConstraintMonomial)), monomialEntry.getValue());

                if (boundNeg) {
                    remainingPoly = remainingPoly.negate();
                }

                newConstraints.put(itpfFactory.createPoly(remainingPoly, ConstraintType.GE, polyInterpretation), positive);

                boundCoeffSum = boundCoeffSum.add(remainingPoly);
            } else {
                hasNonBoundMonomials = true;
            }
        }


        if (foundBound) {
            if (!hasBoundCoeffGtZero && (hasNonBoundMonomials || polyAtom.getConstraintType() == ConstraintType.GT)) {
                newConstraints.put(itpfFactory.createPoly(boundCoeffSum, ConstraintType.GT, polyInterpretation), positive);
            }

            return this.createReplaceData(itpfFactory, ItpfFactory.EMPTY_QUANTORS, newConstraints, ImplicationType.EQUIVALENT, ApplicationMode.SingleStep, false);
        } else {
            return null;
        }

    }

}