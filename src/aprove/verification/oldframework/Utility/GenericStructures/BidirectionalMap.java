package aprove.verification.oldframework.Utility.GenericStructures;

import java.io.*;
import java.util.*;
import java.util.stream.*;

import aprove.verification.oldframework.BasicStructures.*;

/**
 * Straight forward implementation of a bidirectional LinkedHashMap,
 * Every method of LinkedHashMap is reachable by the addtional String LR
 * (mapping from left to right) respectively RL (mapping from right
 * to left). All methods have the same efficiency as the known methods of
 * LinkedHashMap.
 *
 * @author Matthias Sondermann
 * @version $Id$
 * @see LinkedHashMap
 */
public class BidirectionalMap<A, B> implements Serializable {

    private final Map<A, B> lrMap;
    private final Map<B, A> rlMap;

    public BidirectionalMap() {
        this.lrMap = new LinkedHashMap<A, B>();
        this.rlMap = new LinkedHashMap<B, A>();
    }

    public BidirectionalMap(Map<A, B> lrMap) {
        this.lrMap = lrMap;
        this.rlMap = lrMap
            .entrySet()
            .stream()
            .collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey));
    }
    
    public static <A,B> BidirectionalMap<A,B> create(Map<A, B> lrMap) {
        return new BidirectionalMap<A, B>(lrMap);
    }

    public B getLR(A a) {
        return this.lrMap.get(a);
    }

    public A getRL(B b) {
        return this.rlMap.get(b);
    }

    public B putLR(A a, B b) {
        B result = this.lrMap.put(a, b);
        if (result != null) {
            this.rlMap.remove(result);
        }
        this.rlMap.put(b, a);
        return result;
    }

    public A putRL(B b, A a) {
        A result = this.rlMap.put(b, a);
        if (result != null) {
            this.lrMap.remove(result);
        }
        this.lrMap.put(a, b);
        return result;
    }

    public void putAllLR(Map<? extends A, ? extends B> t) {
        for (Map.Entry<? extends A, ? extends B> entry : t.entrySet()) {
            A a = entry.getKey();
            B b = entry.getValue();
            this.putLR(a, b);
        }
    }

    public void putAllRL(Map<? extends B, ? extends A> t) {
        for (Map.Entry<? extends B, ? extends A> entry : t.entrySet()) {
            B b = entry.getKey();
            A a = entry.getValue();
            this.putRL(b, a);
        }
    }

    public Collection<B> valuesLR() {
        return this.lrMap.values();
    }

    public Collection<A> valuesRL() {
        return this.rlMap.values();
    }

    public Set<Map.Entry<A, B>> getEntriesLR() {
        return this.lrMap.entrySet();
    }

    public Set<Map.Entry<B, A>> getEntriesRL() {
        return this.rlMap.entrySet();
    }

    public Set<A> keySetLR() {
        return this.lrMap.keySet();
    }

    public Set<B> keySetRL() {
        return this.rlMap.keySet();
    }

    public Map<A, B> getLRMap() {
        return this.lrMap;
    }

    public Map<B, A> getRLMap() {
        return this.rlMap;
    }

    public boolean containsKeyLR(final A a) {
        return this.lrMap.containsKey(a);
    }

    public boolean containsKeyRL(B b) {
        return this.rlMap.containsKey(b);
    }

    public boolean containsValueLR(B b) {
        return this.rlMap.containsKey(b);
    }

    public boolean containsValueRL(A a) {
        return this.lrMap.containsKey(a);
    }

    public B removeLR(A a) {
        B b = this.lrMap.remove(a);
        if (b != null) {
            this.rlMap.remove(b);
        }
        return b;
    }

    public A removeRL(B b) {
        A a = this.rlMap.remove(b);
        if (a != null) {
            this.lrMap.remove(a);
        }
        return a;
    }

    public int size() {
        return this.lrMap.size();
    }

    public boolean isEmpty() {
        return this.lrMap.isEmpty();
    }

    public void clear() {
        this.lrMap.clear();
        this.rlMap.clear();
    }

    public String toStringLR() {
        StringBuilder sb = new StringBuilder("[");
        Iterator<Map.Entry<A, B>> it = this.lrMap.entrySet().iterator();
        Map.Entry<A, B> actEntry = null;
        if (it.hasNext()) {
            actEntry = it.next();
            sb.append(actEntry.getKey());
            sb.append(" / ");
            sb.append(actEntry.getValue());
        }
        while (it.hasNext()) {
            actEntry = it.next();
            sb.append(", ");
            sb.append(actEntry.getKey());
            sb.append(" / ");
            sb.append(actEntry.getValue());
        }
        sb.append("]");
        return sb.toString();
    }

    public String toStringRL() {
        StringBuilder sb = new StringBuilder("[");
        Iterator<Map.Entry<B, A>> it = this.rlMap.entrySet().iterator();
        Map.Entry<B, A> actEntry = null;
        if (it.hasNext()) {
            actEntry = it.next();
            sb.append(actEntry.getKey());
            sb.append(" / ");
            sb.append(actEntry.getValue());
        }
        while (it.hasNext()) {
            actEntry = it.next();
            sb.append(", ");
            sb.append(actEntry.getKey());
            sb.append(" / ");
            sb.append(actEntry.getValue());
        }
        sb.append("]");
        return sb.toString();
    }

    @Override
    public boolean equals(Object other) {
        if (!(other instanceof BidirectionalMap)) {
            return false;
        }
        BidirectionalMap bm = (BidirectionalMap) other;
        return this.lrMap.equals(bm.lrMap);
    }

    @Override
    public int hashCode() {
        return this.lrMap.hashCode();
    }

    /**
     * Default direction is left to right.
     */
    @Override
    public String toString() {
        return this.toStringLR();
    }
}
