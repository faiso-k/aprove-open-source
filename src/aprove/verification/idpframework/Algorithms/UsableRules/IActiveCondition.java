package aprove.verification.idpframework.Algorithms.UsableRules;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class IActiveCondition extends IDPExportable.IDPExportableSkeleton implements Iterable<Pair<IActiveAtom, Boolean>>, Immutable, IDPExportable, XmlExportable, Comparable<IActiveCondition> {

    public static final IActiveCondition EMPTY_CONDITION = new IActiveCondition();

    public static IActiveCondition create(final IActiveContext activeContext) {
        final Map<IActiveAtom, Boolean> map = new LinkedHashMap<IActiveAtom, Boolean>(activeContext.getContext().size());
        for (final IActiveAtom atom : activeContext.getContext()) {
            IActiveCondition.addToMap(map, atom);
        }
        return new IActiveCondition(ImmutableCreator.create(map));
    }

    public static void addToMap(final Map<IActiveAtom, Boolean> map, final IActiveAtom atom) {
        final Boolean old = map.get(atom);
        if (old != null) {
            map.put(atom, !old);
        } else {
            map.put(atom, Boolean.FALSE);
        }
    }

    private final ImmutableMap<IActiveAtom, Boolean> map;

    protected IActiveCondition() {
        this.map = ImmutableCreator.create(Collections.<IActiveAtom, Boolean>emptyMap());
    }

    protected IActiveCondition(final ImmutableMap<IActiveAtom, Boolean> map) {
        this.map = map;
    }

    public ImmutableMap<IActiveAtom, Boolean> getMap() {
        return this.map;
    }

    public int size() {
        return this.map.size();
    }

    public boolean isEmpty() {
        return this.map.isEmpty();
    }

    public boolean containsAll(final IActiveCondition other) {
        for (final Map.Entry<IActiveAtom, Boolean> otherEntry : other.getMap().entrySet()) {
            final Boolean myValue = this.map.get(otherEntry.getKey());
            if (myValue == null || (otherEntry.getValue() && !myValue)) {
                return false;
            }
        }

        return true;
    }

    public IActiveCondition add(final IActiveAtom atom) {
        final LinkedHashMap<IActiveAtom, Boolean> resMap = new LinkedHashMap<IActiveAtom, Boolean>(this.map);
        IActiveCondition.addToMap(resMap, atom);
        return new IActiveCondition(ImmutableCreator.create(resMap));
    }

    public IActiveCondition addAll(final IActiveContext activeContext) {
        final LinkedHashMap<IActiveAtom, Boolean> resMap = new LinkedHashMap<IActiveAtom, Boolean>(this.map);
        for (final IActiveAtom atom : activeContext.getContext()) {
            IActiveCondition.addToMap(resMap, atom);
        }
        return new IActiveCondition(ImmutableCreator.create(resMap));
    }

    public IActiveCondition addAll(final IActiveCondition activeCondition) {
        final LinkedHashMap<IActiveAtom, Boolean> resMap = new LinkedHashMap<IActiveAtom, Boolean>(this.map);
        for (final Map.Entry<IActiveAtom, Boolean> atom : activeCondition.getMap().entrySet()) {
            IActiveCondition.addToMap(resMap, atom.getKey());
            if (atom.getValue().booleanValue()) {
                IActiveCondition.addToMap(resMap, atom.getKey());
            }
        }
        return new IActiveCondition(ImmutableCreator.create(resMap));
    }


    public IActiveCondition subtract(final IActiveCondition subtrahend) {
        final LinkedHashMap<IActiveAtom, Boolean> resMap = new LinkedHashMap<IActiveAtom, Boolean>(this.map);

        for (final Map.Entry<IActiveAtom, Boolean> subtrahendEntry : subtrahend.getMap().entrySet()) {
            final Boolean myValue = this.map.get(subtrahendEntry.getKey());
            if (myValue == null || (subtrahendEntry.getValue() && !myValue)) {
                throw new IllegalArgumentException("subtraction on atom not possible: " + subtrahendEntry.getKey());
            }

            if (!subtrahendEntry.getValue() && myValue) {
                resMap.put(subtrahendEntry.getKey(), Boolean.FALSE);
            } else {
                resMap.remove(subtrahendEntry.getKey());
            }
        }

        return new IActiveCondition(ImmutableCreator.create(resMap));
    }

    public IActiveCondition replaceFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        final LinkedHashMap<IActiveAtom, Boolean> resMap = new LinkedHashMap<IActiveAtom, Boolean>(this.map);
        boolean changed = false;

        for (final Map.Entry<IActiveAtom, Boolean> atom : resMap.entrySet()) {
            final ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>> fsReplacement = replaceMap.get(atom.getKey().fs);

            if (fsReplacement != null && !fsReplacement.x.equals(atom.getKey().fs)) {
                if (!fsReplacement.y.get(atom.getKey().pos)) {
                    return IActiveCondition.EMPTY_CONDITION;
                }

                int newPos = 0;
                for (int i = atom.getKey().pos - 1; i >= 0; i--) {
                    if (fsReplacement.y.get(i)) {
                        newPos++;
                    }
                }

                resMap.put(IActiveAtom.create(fsReplacement.x, newPos), atom.getValue());
                changed = true;
            } else {
                resMap.put(atom.getKey(), atom.getValue());
            }
        }

        if (changed) {
            return new IActiveCondition(ImmutableCreator.create(resMap));
        } else {
            return this;
        }

    }

    /**
     * not the opposite of add!
     * @param atom
     * @return
     */
    public IActiveCondition delete(final IActiveAtom atom) {
        if (this.map.containsKey(atom)) {
            final LinkedHashMap<IActiveAtom, Boolean> clonedMap = new LinkedHashMap<IActiveAtom, Boolean>(this.map);
            return new IActiveCondition(ImmutableCreator.create(clonedMap));
        }
        return this;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.map == null) ? 0 : this.map.hashCode());
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
        final IActiveCondition other = (IActiveCondition) obj;
        return this.map.equals(other.map);
    }

    @Override
    public Iterator<Pair<IActiveAtom, Boolean>> iterator() {
        final Iterator<Entry<IActiveAtom, Boolean>> iterator = this.map.entrySet().iterator();
        return new Iterator<Pair<IActiveAtom,Boolean>>() {

            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }

            @Override
            public Pair<IActiveAtom, Boolean> next() {
                final Entry<IActiveAtom, Boolean> entry = iterator.next();
                return new Pair<IActiveAtom, Boolean>(entry.getKey(), entry.getValue());
            }

            @Override
            public boolean hasNext() {
                return iterator.hasNext();
            }
        };
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        for (final Map.Entry<IActiveAtom, Boolean> entry : this.map.entrySet()) {
            sb.append(eu.escape("("));
            entry.getKey().export(sb, eu, verbosityLevel);
            sb.append(eu.escape(")"));
            if (entry.getValue().booleanValue()) {
                sb.append(eu.sup("2"));
            }
        }
    }

    @Override
    public Map<String, String> getXmlAttribs(XmlExporter xe) {
        Map<String, String> m = new HashMap<String, String>();
        int index = 0;
        for (final Map.Entry<IActiveAtom, Boolean> entry : this.map.entrySet()) {
            m.put("flag" + index, entry.getValue().toString());
            index++;
        }
        return m;
    }

    @Override
    public XmlContentsMap getXmlContents(XmlExporter xe) {
        XmlContentsMap contents = new XmlContentsMap();
        for (final Map.Entry<IActiveAtom, Boolean> entry : this.map.entrySet()) {
            contents.add(entry.getKey());
        }
        return contents;
    }

    @Override
    public int compareTo(final IActiveCondition o) {
        if (this.containsAll(o)) {
            return 1;
        } else if (o.containsAll(this)) {
            return -1;
        }
        return 0;
    }

}
