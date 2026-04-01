package aprove.verification.idpframework.Polynomials;

import java.util.*;
import java.util.concurrent.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class SharingPolyFactory implements PolyFactory {

    private final ConcurrentMap<Polynomial<?>, Polynomial<?>> polynomials =
        new ConcurrentHashMap<Polynomial<?>, Polynomial<?>>();

    private final ConcurrentMap<Monomial<?>, Monomial<?>> monomials =
        new ConcurrentHashMap<Monomial<?>, Monomial<?>>();

    private final ConcurrentMap<IVariable<?>, IVariable<?>> variables =
        new ConcurrentHashMap<IVariable<?>, IVariable<?>>();

    private final ConcurrentMap<PolyMaxVariable<?>, PolyMaxVariable<?>> maxVariables =
        new ConcurrentHashMap<PolyMaxVariable<?>, PolyMaxVariable<?>>();

    private final ConcurrentMap<SemiRing<?>, Polynomial<?>> zero =
        new ConcurrentHashMap<SemiRing<?>, Polynomial<?>>();

    private final ConcurrentMap<SemiRing<?>, Polynomial<?>> one =
        new ConcurrentHashMap<SemiRing<?>, Polynomial<?>>();

    public SharingPolyFactory() {
    }

    @SuppressWarnings("unchecked")
    @Override
    public <C extends SemiRing<C>> Polynomial<C> create(final C ring, final ImmutableMap<Monomial<C>, C> monomials) {
        final Polynomial<C> poly = Polynomial.create(monomials, this, ring);
        return (Polynomial<C>) this.shareObject(this.polynomials, poly);
    }

    @Override
    public <C extends SemiRing<C>> Polynomial<C> create(final C coeff, final PolyVariable<C> var, final BigInt exp) {
        return this.create(this.createMonomial(coeff.zero(), var, exp), coeff);
    }

    @Override
    public <C extends SemiRing<C>> Polynomial<C> create(final Monomial<C> monom, final C coeff) {
        return this.create(coeff, ImmutableCreator.create(Collections.singletonMap(monom,
            coeff)));
    }

    @Override
    public <C extends SemiRing<C>> Polynomial<C> create(final PolyVariable<C> var) {
        return this.create(Monomial.create(var.getRing(),
            ImmutableCreator.create(Collections.singletonMap(var, BigInt.ONE)),
            this), var.getRing().one());
    }

    @Override
    public <C extends SemiRing<C>> Polynomial<C> create(final C coeff) {
        return this.create(coeff, ImmutableCreator.create(Collections.singletonMap(
            this.emptyMonomial(coeff), coeff)));
    }

    @SuppressWarnings("unchecked")
    @Override
    public <C extends SemiRing<C>> Polynomial<C> zero(final C ring) {
        Polynomial<C> res = (Polynomial<C>) this.zero.get(ring.zero());
        if (res == null) {
            res = this.create(ring.zero());
            res = (Polynomial<C>) this.shareObject(this.polynomials, res);
            this.zero.putIfAbsent(ring.zero(), res);
        }
        return res;
    }

    @SuppressWarnings("unchecked")
    @Override
    public <C extends SemiRing<C>> Polynomial<C> one(final C ring) {
        Polynomial<C> res = (Polynomial<C>) this.one.get(ring.zero());
        if (res == null) {
            res = this.create(ring.one());
            res = (Polynomial<C>) this.shareObject(this.polynomials, res);
            this.one.putIfAbsent(ring.zero(), res);
        }
        return res;
    }

    @Override
    public <C extends SemiRing<C>> Monomial<C> createMonomial(final C ring, final PolyVariable<C> var,
        final BigInt exp) {
        return this.createMonomial(var.getRing(), ImmutableCreator.create(Collections.singletonMap(
            var, exp)));
    }

    @SuppressWarnings("unchecked")
    @Override
    public <C extends SemiRing<C>> Monomial<C> createMonomial(final C ring, final ImmutableMap<? extends PolyVariable<C>, BigInt> variables) {
        final Monomial<C> monomial = Monomial.create(ring, variables, this);
        return (Monomial<C>) this.shareObject(this.monomials, monomial);
    }

    @Override
    public <C extends SemiRing<C>> Monomial<C> emptyMonomial(final C ring) {
        return this.createMonomial(ring, ImmutableCreator.create(Collections.<PolyVariable<C>, BigInt> emptyMap()));
    }

    @SuppressWarnings("unchecked")
    @Override
    public <C extends SemiRing<C>> IVariable<C> createVariable(final String name,
        final SemiRingDomain<C> domain) {
        final IVariable<C> var =
            IVariable.create(name, domain);

        return (IVariable<C>) this.shareObject(this.variables, var);
    }

    @SuppressWarnings("unchecked")
    @Override
    public <C extends SemiRing<C>> PolyMaxVariable<C> createVariable(final C ring, final ImmutableSet<Polynomial<C>> maxs) {
        final PolyMaxVariable<C> var = PolyMaxVariable.create(maxs, this, ring);
        return (PolyMaxVariable<C>) this.shareObject(this.maxVariables, var);
    }

    @Override
    public <C extends SemiRing<C>> Polynomial<C> max(final C ring, final Polynomial<C>... ps) {
        return this.create(this.createVariable(ring, ImmutableCreator.create(new LinkedHashSet<Polynomial<C>>(
            Arrays.asList(ps)))));
    }

    @Override
    public <C extends SemiRing<C>> Polynomial<C> min(final C ring, final Polynomial<C>... ps) {
        final Set<Polynomial<C>> polys = new LinkedHashSet<Polynomial<C>>();
        for (final Polynomial<C> p : ps) {
            polys.add(p.negate());
        }

        return this.create(this.createMonomial(ring,
            this.createVariable(ring, ImmutableCreator.create(polys)), BigInt.ONE),
            ring.one().negate());
    }

    @Override
    public <C extends SemiRing<C>> Polynomial<C> add(final C ring, final Collection<Polynomial<C>> ps) {
        if (ps.isEmpty()) {
            return this.zero(ring);
        }

        final Iterator<Polynomial<C>> pIterator = ps.iterator();

        Polynomial<C> result = pIterator.next();
        while (pIterator.hasNext()) {
            result = result.add(pIterator.next());
        }
        return result;
    }

    @Override
    public <C extends SemiRing<C>> Polynomial<C> mult(final C ring, final Collection<Polynomial<C>> ps) {
        if (ps.isEmpty()) {
            return this.one(ring);
        }
        final Iterator<Polynomial<C>> pIterator = ps.iterator();

        Polynomial<C> result = pIterator.next();
        while (pIterator.hasNext()) {
            result = result.mult(pIterator.next());
        }
        return result;
    }

    private <O> O shareObject(final ConcurrentMap<O, O> pool, final O object) {
        return ConcurrentUtil.addToCache(pool, object, object);
    }

}
