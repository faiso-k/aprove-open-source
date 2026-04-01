package aprove.verification.idpframework.Polynomials;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class DiophantineSplit<C extends SemiRing<C>> {

    /**
     * @param atom
     * @param interpretation
     * @return Map of a Monomial of universally quantified variables to the corresponding coeff just containing existentially quantified variables
     */
    public static <C extends SemiRing<C>> DiophantineSplit<C> create(
        final PolyInterpretation<C> polyInterpretation,
        final ImmutableList<ItpfQuantor> quantifications, final Polynomial<C> poly) {
        final PolyFactory polyFactory = polyInterpretation.getFactory();

        final Map<ImmutableMap<IVariable<C>, BigInt>, Polynomial<C>> diophantineSplit = new LinkedHashMap<ImmutableMap<IVariable<C>, BigInt>, Polynomial<C>>();

        for (final Map.Entry<Monomial<C>, C> monomialCoeff : poly.getMonomials().entrySet()) {

            final ImmutableMap<? extends PolyVariable<C>, BigInt> exponents =
                monomialCoeff.getKey().getExponents();

            final Map<IVariable<C>, BigInt> universalQuantified = new LinkedHashMap<IVariable<C>, BigInt>(exponents.size());
            final Map<IVariable<C>, BigInt> existQuantified = new LinkedHashMap<IVariable<C>, BigInt>(exponents.size());

            for (final Map.Entry<? extends PolyVariable<C>, BigInt> varExponent : exponents.entrySet()) {
                if (!varExponent.getKey().isMax()) {
                    final IVariable<C> var = (IVariable<C>) varExponent.getKey();
                    if (polyInterpretation.isExistQuantified(var)) {
                        existQuantified.put(var, varExponent.getValue());
                    } else {
                        universalQuantified.put(var, varExponent.getValue());
                    }
                } else {
                    throw new IllegalArgumentException("no max variables allowed");
                }
            }

            final Polynomial<C> addPoly = polyFactory.create(polyFactory.createMonomial(poly.getRing(), ImmutableCreator.create(existQuantified)), monomialCoeff.getValue());

            final ImmutableMap<IVariable<C>, BigInt> universalQuantMonomial = ImmutableCreator.create(universalQuantified);

            Polynomial<C> current = diophantineSplit.get(universalQuantMonomial);

            if (current == null) {
                current = addPoly;
            } else {
                current = current.add(addPoly);
            }

            diophantineSplit.put(universalQuantMonomial, current);
        }

        return new DiophantineSplit<C>(poly, ImmutableCreator.create(diophantineSplit));
    }

    private final Polynomial<C> polynomial;
    private final ImmutableMap<ImmutableMap<IVariable<C>, BigInt>, Polynomial<C>> split;

    public DiophantineSplit(final Polynomial<C> polynomial, final ImmutableMap<ImmutableMap<IVariable<C>, BigInt>, Polynomial<C>> split) {
        this.polynomial = polynomial;
        this.split = split;
    }

    public Polynomial<C> getPolynomial() {
        return this.polynomial;
    }

    public ImmutableMap<ImmutableMap<IVariable<C>, BigInt>, Polynomial<C>> getSplit() {
        return this.split;
    }

}
