package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

import java.util.*;

import aprove.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public interface BasicPolySubstitution extends IDPExportable, IBasicSubstitution {

    public boolean substitutesPoly(PolyVariable<?> v);

    public boolean substitutesPoly(Collection<? extends PolyVariable<?>> vs);

    public <C extends SemiRing<C>> Polynomial<C> substitutePoly(PolyVariable<C> v);

    public boolean isEmpty();

    public Set<? extends PolyVariable<?>> getPolyDomain();

    BasicPolySubstitution polyCompose(BasicPolySubstitution sigma);

    public static abstract class BasicPolySubstitutionSkeleton extends AbstractSubstitution<PolyVariable<?>, Polynomial<?>> implements
            BasicPolySubstitution {

        protected BasicPolySubstitutionSkeleton(final ImmutableMap<PolyVariable<?>, Polynomial<?>> map, final boolean cleanMap) {
            super(map, cleanMap);
            if (Globals.useAssertions) {
                for (final Map.Entry<PolyVariable<?>, Polynomial<?>> entry : map.entrySet()) {
                    assert entry.getKey().getRing().isSameRing(entry.getValue().getRing());
                }
            }
        }

        /**
         * @return composed map or null if no changes are made to map
         */
        public static ImmutableMap<PolyVariable<?>, Polynomial<?>> polyCompose(final ImmutableMap<PolyVariable<?>, ? extends Polynomial<?>> map,
            final BasicPolySubstitution sub) {
            boolean changed = false;
            final Map<PolyVariable<?>, Polynomial<?>> newMap = new LinkedHashMap<>();

            for (final Map.Entry<PolyVariable<?>, ? extends Polynomial<?>> entry : map.entrySet()) {
                final PolyVariable<?> key = entry.getKey();
                final Polynomial<?> value = entry.getValue();
                final Polynomial<?> substResult = value.applySubstitution(sub);
                if (!substResult.equals(value)) {
                    changed = true;
                }

                newMap.put(key, substResult);
            }

            for (final PolyVariable<?> key : sub.getPolyDomain()) {
                if (!map.containsKey(key)) {
                    changed = true;
                    newMap.put(key, sub.substitutePoly(key));
                }
            }

            if (changed) {
                return ImmutableCreator.create(newMap);
            } else {
                return null;
            }
        }

    }

}
