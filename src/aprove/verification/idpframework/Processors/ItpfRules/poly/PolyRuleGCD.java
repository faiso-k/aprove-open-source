package aprove.verification.idpframework.Processors.ItpfRules.poly;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
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
public class PolyRuleGCD extends ContextFreeItpfReplaceRule {

    public PolyRuleGCD() {
        super(new ExportableString("PolyRuleGCD"), new ExportableString("ItpfPolyGCD"));
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
        return CompatibleMarkClasses.P_GCD.isCompatible(mark);
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
            final ItpfPolyAtom<BigInt> polyAtom = (ItpfPolyAtom<BigInt>) atom;
            BigInteger gcd = null;
            for (final BigInt coeff : polyAtom.getPoly().getMonomials().values()) {
                if (gcd == null) {
                    gcd = coeff.getBigInt();
                } else {
                    gcd = gcd.gcd(coeff.getBigInt());
                }
            }

            if (gcd != null) {
                gcd = gcd.abs();

                if (!gcd.equals(BigInteger.ONE)) {
                    final PolyInterpretation<BigInt> polyInterpretation = polyAtom.getInterpretation();
                    final ItpfFactory itpfFactory = polyInterpretation.getConstraintFactory();

                    final Map<Monomial<BigInt>, BigInt> newMonomials = new LinkedHashMap<Monomial<BigInt>, BigInt>();

                    for (final Map.Entry<Monomial<BigInt>, BigInt> monomialCoeff : polyAtom.getPoly().getMonomials().entrySet()) {
                        final BigInt newCoeff = BigInt.create(monomialCoeff.getValue().getBigInt().divide(gcd));
                        newMonomials.put(monomialCoeff.getKey(), newCoeff);
                    }

                    final Polynomial<BigInt> newPoly = polyInterpretation.getFactory().create(polyInterpretation.getRing(), ImmutableCreator.create(newMonomials));
                    final ItpfPolyAtom<BigInt> newPolyAtom = itpfFactory.createPoly(newPoly, polyAtom.getConstraintType(), polyAtom.getInterpretation());

                    return this.getSingletonReturn(itpfFactory, newPolyAtom, positive, ImplicationType.EQUIVALENT, ApplicationMode.SingleStep, false);
                }
            }
        }
        return null;
    }

}
