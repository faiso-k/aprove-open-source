package immutables;

import java.util.*;

/**
 * Provides methods to create suitable Immutable* data structures for
 * corresponding mutable data structures (e.g., create returns
 * an ImmutableHashMap when called with a HashMap as argument, but a
 * ImmutableLinkedHashMap when called with a LinkedHashMap as argument).
 *
 * Note that the argument(s) passed to ImmutableCreator.create(...)
 * must not be modified after calling create(...)!
 * If such modifications are desired, pass a
 * (sufficiently deep) copy to create(...).
 *
 * @author Carsten Fuhs, cryingshadow
 * @version $Id$
 */
public abstract class ImmutableCreator {

    /**
     * @param <A> The first component's type.
     * @param <B> The second component's type.
     * @param a The first component.
     * @param b The second component.
     * @return An immutable pair with the specified components.
     */
    public static <A,B> ImmutablePair<A,B> create(A a, B b) {
        return new ImmutablePair<A,B>(a, b);
    }

    /**
     * @param <A> The first component's type.
     * @param <B> The second component's type.
     * @param <C> The third component's type.
     * @param a The first component.
     * @param b The second component.
     * @param c The third component.
     * @return An immutable triple with the specified components.
     */
    public static <A,B,C> ImmutableTriple<A,B,C> create(A a, B b, C c) {
        return new ImmutableTriple<A,B,C>(a, b, c);
    }

    /**
     * @param <E> The type of the deque's elements.
     * @param arrayDeque The ArrayDeque to be made immutable.
     * @return An immutable version of the specified ArrayDeque.
     */
    public static <E> ImmutableArrayDeque<E> create(ArrayDeque<E> arrayDeque) {
        if (arrayDeque instanceof ImmutableArrayDeque) {
            return (ImmutableArrayDeque<E>) arrayDeque;
        } else {
            return ImmutableArrayDeque.create(arrayDeque);
        }
    }

    /**
     * @param <E> The type of the list's elements.
     * @param arrayList The ArrayList to be made immutable.
     * @return An immutable version of the specified ArrayList.
     */
    public static <E> ImmutableArrayList<E> create (ArrayList<E> arrayList) {
        if (arrayList instanceof ImmutableArrayList) {
            return (ImmutableArrayList<E>) arrayList;
        } else {
            return ImmutableArrayList.create(arrayList);
        }
    }

    /**
     * @param <E> The type of the collection's elements.
     * @param coll The Collection to be made immutable.
     * @return An immutable version of the specified Collection.
     */
    public static <E> ImmutableCollection<E> create(Collection<E> coll) {
        if (coll instanceof ImmutableCollection) {
            return (ImmutableCollection<E>)coll;
        } else if (coll instanceof Set) {
            return ImmutableCreator.create((Set<E>)coll);
        } else if (coll instanceof List) {
            return ImmutableCreator.create((List<E>)coll);
        } else if (coll instanceof Deque) {
            return ImmutableCreator.create((Deque<E>)coll);
        } else {
            return DefaultImmutableCollection.create(coll);
        }
    }

    /**
     * @param <E> The type of the deque's elements.
     * @param deque The Deque to be made immutable.
     * @return An immutable version of the specified Deque.
     */
    public static <E> ImmutableDeque<E> create(Deque<E> deque) {
        if (deque instanceof ImmutableDeque) {
            return (ImmutableDeque<E>) deque;
        } else if (deque instanceof ArrayDeque) {
            return ImmutableCreator.create((ArrayDeque<E>)deque);
        } else {
            return DefaultImmutableDeque.create(deque);
        }
    }

    /**
     * @param <K> The type of the map's keys.
     * @param <V> The type of the map's values.
     * @param map The HashMap to be made immutable.
     * @return An immutable version of the specified HashMap.
     */
    public static <K,V> ImmutableHashMap<K,V> create(HashMap<K,V> map) {
        if (map instanceof ImmutableHashMap) {
            return (ImmutableHashMap<K,V>) map;
        } else {
            return ImmutableHashMap.create(map);
        }
    }

    /**
     * @param <E> The type of the set's elements.
     * @param set The HashSet to be made immutable.
     * @return An immutable version of the specified HashSet.
     */
    public static <E> ImmutableHashSet<E> create(HashSet<E> set) {
        if (set instanceof ImmutableHashSet) {
            return (ImmutableHashSet<E>) set;
        } else {
            return ImmutableHashSet.create(set);
        }
    }

    /**
     * @param <K> The type of the map's keys.
     * @param <V> The type of the map's values.
     * @param map The LinkedHashMap to be made immutable.
     * @return An immutable version of the specified LinkedHashMap.
     */
    public static <K,V> ImmutableLinkedHashMap<K,V> create(LinkedHashMap<K,V> map) {
        if (map instanceof ImmutableLinkedHashMap) {
            return (ImmutableLinkedHashMap<K,V>) map;
        } else {
            return ImmutableLinkedHashMap.create(map);
        }
    }

    /**
     * @param <E> The type of the set's elements.
     * @param set The LinkedHashSet to be made immutable.
     * @return An immutable version of the specified LinkedHashSet.
     */
    public static <E> ImmutableLinkedHashSet<E> create(LinkedHashSet<E> set) {
        if (set instanceof ImmutableLinkedHashSet) {
            return (ImmutableLinkedHashSet<E>) set;
        } else {
            return ImmutableLinkedHashSet.create(set);
        }
    }

    /**
     * @param <E> The type of the list's elements.
     * @param linkedList The LinkedList to be made immutable.
     * @return An immutable version of the specified LinkedList.
     */
    public static <E> ImmutableLinkedList<E> create(LinkedList<E> linkedList) {
        if (linkedList instanceof ImmutableLinkedList) {
            return (ImmutableLinkedList<E>) linkedList;
        } else {
            return ImmutableLinkedList.create(linkedList);
        }
    }

    /**
     * @param <E> The type of the list's elements.
     * @param list The List to be made immutable.
     * @return An immutable version of the specified List.
     */
    public static <E> ImmutableList<E> create(List<E> list) {
        if (list instanceof ImmutableList) {
            return (ImmutableList<E>) list;
        } else if (list instanceof ArrayList) {
            return ImmutableCreator.create((ArrayList<E>) list);
        } else {
            return DefaultImmutableList.create(list);
        }
    }

    /**
     * @param <K> The type of the map's keys.
     * @param <V> The type of the map's values.
     * @param map The Map to be made immutable.
     * @return An immutable version of the specified Map.
     */
    public static <K,V> ImmutableMap<K,V> create(Map<K,V> map) {
        if (map instanceof ImmutableMap) {
            return (ImmutableMap<K,V>)map;
        } else if (map instanceof LinkedHashMap) {
            return ImmutableCreator.create((LinkedHashMap<K,V>) map);
        } else if (map instanceof HashMap) {
            return ImmutableCreator.create((HashMap<K,V>) map);
        } else {
            return DefaultImmutableMap.create(map);
        }
    }

    /**
     * @param <E> The type of the set's elements.
     * @param set The NavigableSet to be made immutable.
     * @return An immutable version of the specified NavigableSet.
     */
    public static <E> ImmutableNavigableSet<E> create(NavigableSet<E> set) {
        if (set instanceof ImmutableNavigableSet) {
            return (ImmutableNavigableSet<E>)set;
        } else if (set instanceof TreeSet) {
            return ImmutableCreator.create((TreeSet<E>) set);
        } else {
            return DefaultImmutableNavigableSet.create(set);
        }
    }

    /**
     * @param <E> The type of the set's elements.
     * @param set The Set to be made immutable.
     * @return An immutable version of the specified Set.
     */
    public static <E> ImmutableSet<E> create(Set<E> set) {
        if (set instanceof ImmutableSet) {
            return (ImmutableSet<E>)set;
        } else if (set instanceof SortedSet) {
            return ImmutableCreator.create((SortedSet<E>) set);
        } else if (set instanceof LinkedHashSet) {
            return ImmutableCreator.create((LinkedHashSet<E>) set);
        } else if (set instanceof HashSet) {
            return ImmutableCreator.create((HashSet<E>) set);
        } else {
            return DefaultImmutableSet.create(set);
        }
    }

    /**
     * @param <E> The type of the set's elements.
     * @param set The SortedSet to be made immutable.
     * @return An immutable version of the specified SortedSet.
     */
    public static <E> ImmutableSortedSet<E> create(SortedSet<E> set) {
        if (set instanceof ImmutableSortedSet) {
            return (ImmutableSortedSet<E>)set;
        } else if (set instanceof NavigableSet) {
            return ImmutableCreator.create((NavigableSet<E>) set);
        } else {
            return DefaultImmutableSortedSet.create(set);
        }
    }

    /**
     * @param <E> The type of the set's elements.
     * @param set The TreeSet to be made immutable.
     * @return An immutable version of the specified TreeSet.
     */
    public static <E> ImmutableTreeSet<E> create(TreeSet<E> set) {
        if (set instanceof ImmutableTreeSet) {
            return (ImmutableTreeSet<E>)set;
        } else {
            return ImmutableTreeSet.create(set);
        }
    }

    public static <E> ImmutableStack<E> create(final Stack<E> stack) {
        return ImmutableStack.create(stack);
    }
}
