package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public abstract class AbstractSubstitution<K extends IDPExportable, V extends IDPExportable> extends IBasicSubstitution.IBasicSubstitutionSkeleton {
    /*
     * real values
     */
    protected final ImmutableMap<K, ? extends V> rawMap;

    /*
     * cached/computed values
     */
    private ImmutableMap<K, ? extends V> cachedMap;

    /**
     * creates a substitution from a non-null map
     * @param map
     * @param cleanMap True if and only if map does not contain identity
     * entries.
     */
    protected AbstractSubstitution(final ImmutableMap<K, ? extends V> map,
        final boolean cleanMap) {
        if (Globals.useAssertions) {
            assert (map != null);
            if (cleanMap) {
                for (final Map.Entry<K, ? extends V> entry : map.entrySet()) {
                    assert (!entry.getKey().equals(entry.getValue())) : "unclean map while cleanMap = true";
                }
            }
        }
        this.rawMap = map;
        if (cleanMap) {
            this.cachedMap = map;
        }
    }

    /**
     * gives the result of applying this on the given K v or null
     * @param v
     */
    protected V substitute(final K v) {
        final V subst = this.rawMap.get(v);
        return subst;
    }

    /**
     * @param v
     */
    protected boolean substitutes(final K v) {
        return this.rawMap.containsKey(v);
    }

    /**
     * returns the substitution as a map
     */
    public ImmutableMap<K, ? extends V> getMap() {
        if (this.cachedMap == null) {
            final Map<K, V> map = new LinkedHashMap<K, V>();
            for (final Map.Entry<K, ? extends V> entry : this.rawMap.entrySet()) {
                final K key = entry.getKey();
                final V value = entry.getValue();
                if (!key.equals(value)) {
                    map.put(key, value);
                }
            }
            this.cachedMap = ImmutableCreator.create(map);
        }
        return this.cachedMap;
    }

    public boolean isEmpty() {
        return this.getMap().isEmpty();
    }


    @Override
    public Set<?> getDomain() {
        return this.getMap().keySet();
    }

    @Override
    public Object substitute(final Object key) {
        return this.getMap().get(key);
    }

    @Override
    public void export(final StringBuilder sb, final Export_Util eu, final VerbosityLevel verbosity) {
        AbstractSubstitution.export(this.getMap(), sb, eu, verbosity);
    }

    public static void export(final Map<? extends IDPExportable, ? extends IDPExportable> map, final StringBuilder sb, final Export_Util eu, final VerbosityLevel verbosityLevel) {
        if (map.isEmpty()) {
            sb.append("[ ]");
            return;
        }

        sb.append("[");
        for (final Map.Entry<? extends IDPExportable, ? extends IDPExportable> entry : map.entrySet()) {
            entry.getKey().export(sb, eu, verbosityLevel);
            sb.append(" / ");
            entry.getValue().export(sb, eu, verbosityLevel);
            sb.append(", ");
        }
        sb.setLength(sb.length() - 2);
        sb.append("]");
    }

}
