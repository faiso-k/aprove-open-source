package aprove.verification.idpframework.Core.Utility;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public class CollectionUtil {

    public static Set<IFunctionSymbol<?>> getRootSymbols(final Iterable<? extends HasRootSymbol<?>> hasRoots) {
        final Set<IFunctionSymbol<?>> roots = new HashSet<IFunctionSymbol<?>>();
        for (final HasRootSymbol<?> t : hasRoots) {
            roots.add(t.getRootSymbol());
        }
        return roots;
    }

    public static Set<IVariable<?>> getVariables(final Iterable<? extends HasVariables<?>> terms) {
        final Set<IVariable<?>> vars = new HashSet<IVariable<?>>();
        for (final HasVariables<?> t : terms) {
            vars.addAll(t.getVariables());
        }
        return vars;
    }

    public static <T extends HasVariables<?>> Set<IVariable<?>> getMarkVariables(final Collection<? extends MarkContent<?, T>> marks) {
        final Set<IVariable<?>> vars = new HashSet<IVariable<?>>();
        for (final MarkContent<?, T> mark : marks) {
            for (final HasVariables<?> t : mark) {
                vars.addAll(t.getVariables());
            }
        }
        return vars;
    }

    public static <K, V> ImmutableMap<K, ImmutableSet<V>> immutableCollectionMap(final CollectionMap<K, V> map) {
        final LinkedHashMap<K, ImmutableSet<V>> res = new LinkedHashMap<K, ImmutableSet<V>>();

        for (final Map.Entry<K, Collection<V>> c : map.entrySet()) {
            res.put(c.getKey(), ImmutableCreator.create((Set<V>) c.getValue()));
        }

        return ImmutableCreator.create(res);
    }

    public static <K, V> Map<K, ImmutableSet<V>> immutableSetMap(final Map<K, ? extends Set<V>> map) {
        final Map<K, ImmutableSet<V>> res = new LinkedHashMap<K, ImmutableSet<V>>();

        for (final Map.Entry<K, ? extends Set<V>> mapEntry : map.entrySet()) {
            res.put(mapEntry.getKey(), ImmutableCreator.create(mapEntry.getValue()));
        }

        return res;
    }

}
