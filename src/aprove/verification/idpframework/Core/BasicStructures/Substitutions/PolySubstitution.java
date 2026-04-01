package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

import java.util.*;

import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class PolySubstitution extends
        BasicPolySubstitution.BasicPolySubstitutionSkeleton implements
        ImmutablePolySubstitution {

    /**
     * creates a substitution from a non-null map
     * @param map
     */
    public static PolySubstitution create(final ImmutableMap<PolyVariable<?>, Polynomial<?>> map,
        final boolean cleanMap) {

        return new PolySubstitution(map, cleanMap);
    }

    /**
     * creates a substitution [x / poly]
     */
    public static <C extends SemiRing<C>> PolySubstitution create(final PolyVariable<C> x,
        final Polynomial<C> poly) {
        final Map<PolyVariable<?>, Polynomial<?>> map =
            java.util.Collections.<PolyVariable<?>, Polynomial<?>> singletonMap(
                x, poly);
        return new PolySubstitution(ImmutableCreator.create(map), true);
    }

    public static PolySubstitution EMPTY_SUBSTITUTION =
        new PolySubstitution(
            ImmutableCreator.create(Collections.<PolyVariable<?>, Polynomial<?>> emptyMap()),
            true);

    protected PolySubstitution(
            final ImmutableMap<PolyVariable<?>, Polynomial<?>> map,
            final boolean cleanMap) {
        super(map, cleanMap);
    }

    @Override
    public boolean substitutesPoly(final PolyVariable<?> v) {
        return this.getMap().containsKey(v);
    }

    @Override
    public boolean substitutesPoly(final Collection<? extends PolyVariable<?>> vs) {
        for (final PolyVariable<?> v : vs) {
            if (this.substitutesPoly(v)) {
                return true;
            }
        }
        return false;
    }

    @SuppressWarnings("unchecked")
    @Override
    public <R extends SemiRing<R>> Polynomial<R> substitutePoly(final PolyVariable<R> v) {
        if (this.substitutesPoly(v)) {
            return (Polynomial<R>) this.substitute(v);
        } else {
            return null;
        }
    }

    @Override
    public Set<PolyVariable<?>> getPolyDomain() {
        return this.getMap().keySet();
    }

    /**
     * returns the composition of this substitution with the given substitution.
     */
    @Override
    public PolySubstitution polyCompose(final BasicPolySubstitution sub) {
        if (sub.isEmpty()) {
            return this;
        }

        final ImmutableMap<PolyVariable<?>, ? extends Polynomial<?>> myMap = this.getMap();
        final ImmutableMap<PolyVariable<?>, Polynomial<?>> newMap = BasicPolySubstitutionSkeleton.polyCompose(myMap, sub);

        if (newMap != null) {
            return PolySubstitution.create(newMap, true);
        } else {
            return this;
        }
    }

    @Override
    public ImmutablePolySubstitution immutablePolyCompose(final BasicPolySubstitution sigma) {
        return this.polyCompose(sigma);
    }

}
