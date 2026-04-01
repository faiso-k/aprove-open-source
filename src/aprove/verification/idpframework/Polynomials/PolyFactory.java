package aprove.verification.idpframework.Polynomials;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public interface PolyFactory {

    public <C extends SemiRing<C>> IVariable<C> createVariable(String name,
        SemiRingDomain<C> domain);

    public <C extends SemiRing<C>> PolyMaxVariable<C> createVariable(C ring, final ImmutableSet<Polynomial<C>> maxs);

    public <C extends SemiRing<C>> Monomial<C> emptyMonomial(C ring);
    public <C extends SemiRing<C>> Monomial<C> createMonomial(C ring, final PolyVariable<C> var,
        final BigInt exp);
    public <C extends SemiRing<C>> Monomial<C> createMonomial(C ring, ImmutableMap<? extends PolyVariable<C>, BigInt> immutableMap);

    public <C extends SemiRing<C>> Polynomial<C> create(C ring, ImmutableMap<Monomial<C>, C> monomials);
    public <C extends SemiRing<C>> Polynomial<C> create(final Monomial<C> monom, final C coeff);
    public <C extends SemiRing<C>> Polynomial<C> create(final PolyVariable<C> var);
    public <C extends SemiRing<C>> Polynomial<C> create(C coeff, final PolyVariable<C> var,  BigInt exp);
    public <C extends SemiRing<C>> Polynomial<C> create(C coeff);

    public <C extends SemiRing<C>> Polynomial<C> zero(C ring);

    public <C extends SemiRing<C>> Polynomial<C> one(C ring);

    public <C extends SemiRing<C>> Polynomial<C> max(C ring, Polynomial<C>... ps);
    public <C extends SemiRing<C>> Polynomial<C> min(C ring, Polynomial<C>... ps);

    public <C extends SemiRing<C>> Polynomial<C> add(C ring, Collection<Polynomial<C>> ps);
    public <C extends SemiRing<C>> Polynomial<C> mult(C ring, Collection<Polynomial<C>> ps);

}
