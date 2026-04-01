package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

import aprove.*;

/** Implementation of a multiset as a mapping from elements to integers.
 *  This implementation is backed by a hashtable.
 *
 *  @author  Peter Schneider-Kamp
 *  @version $Id$
 */

public class HashMultiSet<T> extends LinkedHashMap<T, Integer> implements MultiSet<T> {

    public HashMultiSet() {
        super();
    }

    public HashMultiSet(int initialCapacity) {
        super(initialCapacity);
    }

    public HashMultiSet(Map<T, Integer> other) {
        super(other);
        if (Globals.useAssertions) {
            assert (this.sanityCheck());
        }
    }

    public HashMultiSet(Collection<? extends T> other) {
        super();
        for (T elem : other) {
            this.add(elem);
        }
    }

    private boolean sanityCheck() {
        for (Integer num : this.values()) {
            if (num == null) {
                return false;
            }
            if (num < 1) {
                return false;
            }
        }
        return true;
    }

    @Override
    public int add(T e) {
        return this.add(e, 1);
    }

    @Override
    public int add(T e, int occ) {
        if (Globals.useAssertions) {
            assert (occ >= 0);
        }
        if (occ == 0) {
            return 0;
        }
        Integer num = this.get(e);
        if (num != null) {
            occ += num;
        }
        this.put(e, occ);
        return occ;
    }

    @Override
    public int removeOne(T e) {
        return this.remove(e, 1);
    }

    @Override
    public int remove(T e, int occ) {
        if (Globals.useAssertions) {
            assert (occ >= 0);
        }
        if (occ == 0) {
            return 0;
        }
        Integer num = this.get(e);
        if (num == null) {
            return 0;
        }
        int newNum = num - occ;
        if (newNum < 1) {
            super.remove(e);
            return num;
        }
        this.put(e, newNum);
        return occ;
    }

    @Override
    public int removeAny(T e) {
        Integer num = super.remove(e);
        if (num == null) {
            return 0;
        } else {
            return num;
        }
    }

    @Override
    public int frequency(T e) {
        Integer num = this.get(e);
        if (num == null) {
            return 0;
        }
        return num;
    }

    @Override
    public boolean contains(T e) {
        return this.get(e) != null;
    }

    @Override
    public boolean containsAll(MultiSet<T> other) {
        for (Map.Entry<T, Integer> entry : other.entrySet()) {
            Integer thisCount = super.get(entry.getKey());
            if (thisCount == null || thisCount < entry.getValue()) {
                return false;
            }
        }
        return true;
    }

    @Override
    public void addAll(MultiSet<T> other) {
        for (Map.Entry<T, Integer> entry : other.entrySet()) {
            this.add(entry.getKey(), entry.getValue());
        }
    }

    @Override
    public MultiSet<T> union(MultiSet<T> other) {
        MultiSet<T> res = new HashMultiSet<T>(this);
        res.addAll(other);
        return res;
    }

    @Override
    public void retainAll(MultiSet<T> other) {
        Iterator<Map.Entry<T, Integer>> i = this.entrySet().iterator();
        while (i.hasNext()) {
            Map.Entry<T, Integer> entry = i.next();
            T elem = entry.getKey();
            Integer otherNum = other.get(elem);
            if (otherNum == null) {
                i.remove();
            } else {
                int thisNum = entry.getValue();
                if (otherNum < thisNum) {
                    entry.setValue(otherNum);
                }
            }
        }
    }

    @Override
    public MultiSet<T> intersect(MultiSet<T> other) {
        int sizeThis = super.size();
        int sizeOther = other.size();
        MultiSet<T> res;
        if (sizeThis < sizeOther) {
            res = new HashMultiSet<T>(this);
            res.retainAll(other);
        } else {
            res = new HashMultiSet<T>(other);
            res.retainAll(this);
        }
        return res;
    }

    @Override
    public void removeAll(MultiSet<T> other) {
        for (Map.Entry<T, Integer> entry : other.entrySet()) {
            this.remove(entry.getKey(), entry.getValue());
        }
    }

    @Override
    public MultiSet<T> subtract(MultiSet<T> other) {
        MultiSet<T> res = new HashMultiSet<T>(this);
        res.removeAll(other);
        return res;
    }

    @Override
    public List<T> toList() {
        List<T> res = new ArrayList<T>();
        for (Map.Entry<T, Integer> entry : this.entrySet()) {
            T elem = entry.getKey();
            int num = entry.getValue();
            for (int i = 0; i < num; i++) {
                res.add(elem);
            }
        }
        return res;
    }

    @Override
    public int multiSize() {
        int res = 0;
        for (Integer num : this.values()) {
            res += num;
        }
        return res;
    }

    @Override
    public Integer put(T e, Integer occ) {
        if (Globals.useAssertions) {
            assert (occ != null);
            assert (occ > 0);
        }
        return super.put(e, occ);
    }

    @Override
    public boolean isSubsetOf(MultiSet<T> other) {
        for (Map.Entry<T, Integer> entry : this.entrySet()) {
            if (entry.getValue().intValue() > other.frequency(entry.getKey())) {
                return false;
            }
        }
        return true;
    }

}
