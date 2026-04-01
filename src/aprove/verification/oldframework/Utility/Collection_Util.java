package aprove.verification.oldframework.Utility;

import java.util.*;
import java.util.concurrent.ConcurrentHashMap;

import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author thiemann
 */
public abstract class Collection_Util {
    /**
     * Computes whether two collections are disjoint
     */
    public static boolean areDisjoint(final Collection c1, final Collection c2) {
        final Iterator i = c1.iterator();
        while (i.hasNext()) {
            final Object elem = i.next();
            if (c2.contains(elem)) {
                return false;
            }
        }
        return true;
    }

    public static <E extends Comparable<? super E>> E getMaximum(final Collection<E> coll) {
        if (coll.isEmpty()) {
            return null;
        }
        E max = coll.iterator().next();
        for (final E e : coll) {
            if (e.compareTo(max) > 0) {
                max = e;
            }
        }
        return max;
    }

    /**
     * returns those sets of c that are a superset of s
     */
    public static <E> Set<Set<E>> getSuperSetsOf(final Set<E> s, final Collection<Set<E>> c) {
        final Set<Set<E>> sss = new HashSet<Set<E>>();
        for (final Set<E> ss : c) {
            if (ss.containsAll(s)) {
                sss.add(ss);
            }
        }
        return sss;
    }

    /**
     * returns true iff ss is a superset of some set of c
     */
    public static <E> boolean isSuperSetOf(final Set<E> ss, final Collection<Set<E>> c) {
        for (final Set<E> s : c) {
            if (ss.containsAll(s)) {
                return true;
            }
        }
        return false;
    }

    public static <E> void crossProduct(final Collection[] css, final Combinator<E> comb, final Collection<E> target) {
        final int size = css.length;
        final Iterator[] its = new Iterator[size];
        final Object[] currentOs = new Object[size];
        for (int i = 0; i < size; i++) {
            its[i] = css[i].iterator();
            if (its[i].hasNext()) {
                currentOs[i] = its[i].next();
            } else {
                return; // one set empty => no output;
            }
        }
        target.add(comb.combine(currentOs));
        while (true) {
            int i = 0;
            boolean carry = false;
            do { // count up, one step
                if (i >= size) {
                    return;
                }
                if (its[i].hasNext()) {
                    currentOs[i] = its[i].next();
                    carry = false;
                } else {
                    its[i] = css[i].iterator();
                    currentOs[i] = its[i].next(); // no set is empty, so no check needed
                    carry = true;
                    i++;
                }
            } while (carry);
            target.add(comb.combine(currentOs));
        }
    }

    public interface Combinator<E> {
        public E combine(Object[] tup);
    }

    /**
     * @param collection some collection
     * @return a list with { (x, y) | x, y \in collection, pos(x) < pos(y) }
     * where pos(x) is the position of x as defined by the iterator of the
     * collection
     * @param <X> the type of the elements
     */
    public static <X> List<Pair<X, X>> getPairs(final Collection<X> collection) {
        final List<X> list = new ArrayList<>(collection);
        final List<Pair<X, X>> result = new LinkedList<>();
        for (int i = 0; i < list.size(); i++) {
            final X elemI = list.get(i);
            for (int j = i + 1; j < list.size(); j++) {
                result.add(new Pair<>(elemI, list.get(j)));
            }
        }
        return result;
    }

    public static <E, C extends Collection<E>> List<C> subcollection(Collection<E> s, CollectionCreator<E, C> creater) {
        List<C> res = new ArrayList<>();
        res.add(creater.create());
        List<C> toAdd = new ArrayList<>();
        for (E e: s) {
            for (C subres: res) {
                C with = creater.create();
                with.addAll(subres);
                with.add(e);
                toAdd.add(with);
            }
            res.addAll(toAdd);
            toAdd.clear();
        }
        return res;
    }

    public static <T> List<? extends List<T>> sublists(List<T> s) {
            return Collection_Util.subcollection(s, CollectionCreator.<T>arrayList());
    }

    public static <T> List<? extends Set<T>> subsets(Set<T> s) {
        return subcollection(s, CollectionCreator.<T>linkedHashSet());
    }

    public static <T> Set<T> intersection(Collection<T> xs, Collection<T> ys) {
        Set<T> intersection = new LinkedHashSet<>(xs);
        intersection.retainAll(ys);
        return intersection;
    }

    @SafeVarargs
    public static <T> Set<T> union(Collection<? extends T>... xss) {
        Set<T> union = new LinkedHashSet<>();
        for (Collection<? extends T> xs: xss) {
            union.addAll(xs);
        }
        return union;
    }

    public static <T> Set<T> difference(Collection<? extends T> xs, Collection<? extends T> ys) {
        Set<T> difference = new LinkedHashSet<>(xs);
        difference.removeAll(ys);
        return difference;
    }

    /**
     * @return a new empty concurrent set
     */
    public static <T> Set<T> createConcurrentHashSet() {
        return ConcurrentHashMap.newKeySet();
    }

    /**
     * Constructs a new concurrent set containing the elements of the specified collection
     * @param c the collection whose elements are to be placed into the set
     * @return the created set
     */
    public static <T> Set<T> createConcurrentHashSet(Collection<T> c) {
        Set<T> result = ConcurrentHashMap.newKeySet(c.size());
        result.addAll(c);
        return result;
    }
}
