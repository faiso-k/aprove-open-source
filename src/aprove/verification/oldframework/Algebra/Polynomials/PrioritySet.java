package aprove.verification.oldframework.Algebra.Polynomials;

import java.util.*;

import aprove.*;

/**
 * @author Carsten Fuhs
 * @version $Id$
 *
 * Objects of type PrioritySet<T> may contain Objects of type T 0 or 1 time,
 * and the objects are accessible according to the order imposed by a
 * Comparator. Note that this Comparator need not be consistent with equals
 * (as opposed to e.g. Comparators used for SortedSet).
 */
public class PrioritySet<T> implements Set<T> {

    // These two attributes are to be kept consistent by all methods,
    // i.e. any object of type T must occur either in both or none of
    // them before and after the invocation of any method of this.
    private LinkedList<T> queue; // for the ordered aspect of this
    private Set<T> set; // for the set aspect of this

    private Comparator<T> comparator;
    // the underlying Comparator, need not be consistent with equals

    // So far, we include set as (Linked)HashSet for the sake of being
    // able to test containment in this efficiently; using queue.contains(...)
    // instead and omitting set might be faster, though (yet to be tested).



    /**
     * Creates an empty PrioritySet with comparator as underlying Comparator.
     *
     * @param comparator  the comparator to be used
     */
    public PrioritySet(Comparator<T> comparator) {
        this(comparator, new LinkedHashSet<T>());
    }

    /**
     * Creates a PrioritySet with comparator as Comparator and elements
     * as initially contained elements.
     *
     * @param comparator  the comparator to be used
     * @param elements  the elements to be contained by this
     */
    public PrioritySet(Comparator<T> comparator, Set<T> elements) {
        this.comparator = comparator;
        this.set = new LinkedHashSet<T>(elements);
        this.queue = new LinkedList<T>();
        this.queue.addAll(this.set);
    }


    @Override
    public void clear() {
        this.set.clear();
        this.queue.clear();
    }

    /**
     * @param t  to be checked for containment in this
     * @return whether this contains t
     */
    @Override
    public boolean contains (Object t) {
        return this.set.contains(t);
    }

    /**
     * Untested. Use with caution.
     * @param coll
     * @return
     */
    @Override
    public boolean containsAll(Collection<?> coll) {
        for (Object element : coll) {
            if (! this.contains(element)) {
                return false;
            }
        }
        return true;
    }

    /**
     * @return whether this is empty (has no elements)
     */
    @Override
    public boolean isEmpty() {
        return this.set.isEmpty();
    }


    /**
     * Removes and returns a minimal element (according to the Comparator
     * that has been used for constructing this) of this.
     *
     * @return a minimal element of this or null if this does not contain
     *  any elements
     */
    public T poll() {
        T result = this.queue.poll();
        if (result != null) { // there is s.th. to be removed
            this.set.remove(result);
        }
        return result; // doesn't matter whether it is null, just return it
    }

    /**
     * Untested. Use with caution.
     * @param o
     * @return
     */
    @Override
    public boolean remove(Object o) {
        boolean result = this.set.remove(o);
        if (result) {
            this.queue.remove(o);
        }
        return result;
    }

    /**
     * Untested. Use with caution.
     * @param coll
     * @return
     */
    @Override
    public boolean removeAll(Collection<?> coll) {
        boolean result = false;
        for (Object element : coll) {
            result = this.remove(element) || result;
            // note the order of the operands of "||"!
        }
        return result;
    }

    /**
     * Untested. Use with caution.
     * @param coll
     * @return
     */
    @Override
    public boolean retainAll(Collection<?> coll) {
        boolean result = false;
        Iterator<T> iter = this.iterator();
        while (iter.hasNext()) {
            T element = iter.next();
            if (! coll.contains(element)) {
                iter.remove();
                result = true;
            }
        }
        return result;
    }

    /**
     * Adds t to this if t is not already contained by this and
     * returns whether an actual addition has taken place.
     *
     * @param t  to be added to this
     * @return whether an actual addition has taken place
     */
    @Override
    public boolean add(T t) {
        if (! this.set.contains(t)) {
            this.set.add(t);

            ListIterator<T> listIter = this.queue.listIterator();
            boolean insertionDone = false;
            while (listIter.hasNext()) {
                T currentElement = listIter.next();
                if (this.comparator.compare(currentElement, t) >= 0) {
                    listIter.add(t);
                    insertionDone = true;
                    break;
                }
            }
            if (! insertionDone) {
                this.queue.add(t);
            }

            return true;
        }
        else {
            return false;
        }
    }

    /**
     * Adds all elements of t that are not already present anyway.
     *
     * @param t  iterable object of objects that are to be added to this.
     *  Must not be null.
     * @return whether an actual addition has taken place
     */
    @Override
    public boolean addAll(Collection<? extends T> t) {
        boolean result = false;
        for (T element : t) { // do it this way to avoid duplicates
            result = this.add(element) || result;
        }
        return result;
    }

    /**
     * Untested. Use with caution.
     * @param <E>
     * @param array
     * @return
     */
    @Override
    public <E> E[] toArray(E[] array) {
        int size = this.size();
        if (array.length < size) {
            array = (E[]) java.lang.reflect.Array.newInstance(array.getClass().getComponentType(), size);
        }
        Object[] result = array; // this looks a little nasty.
        int i = 0;
        for (T element : this) {
            result[i++] = element;
        }
        if (array.length > size) {
            array[size] = null;
        }
        return array; // that's why the "result" stuff is nasty.
    }

    /**
     * Untested. Use with caution.
     * @return an array that contains all the elements of this.
     */
    @Override
    public Object[] toArray() {
        Object[] result = new Object[this.size()];
        Iterator<T> iter = this.iterator();
        for (int i = 0; i < result.length; ++i) {
            T nextOne = iter.next();
            result[i] = nextOne;
        }
        if (Globals.useAssertions) {
            assert ! iter.hasNext();
        }
        return result;
    }

    /**
     * Returns how many elements this contains.
     *
     * @return how many elements this contains
     */
    @Override
    public int size() {
        return this.set.size();
    }

    @Override
    public String toString() {
        return this.queue.toString();
    }

    /**
     * @return a new Iterator over this.
     */
    @Override
    public Iterator<T> iterator() {
        return new Itr();
    }


    /**
     * Needed for the iterator() method of PrioritySet.
     */
    private class Itr implements Iterator<T> {

        private Iterator<T> queueIter;
        private T currentElement;

        public Itr() {
            this.queueIter = PrioritySet.this.queue.iterator();
            this.currentElement = null;
        }

        @Override
        public boolean hasNext() {
            return this.queueIter.hasNext();
        }

        @Override
        public T next() {
            this.currentElement = this.queueIter.next();
            return this.currentElement;
        }

        @Override
        public void remove() {
            this.queueIter.remove();
            PrioritySet.this.set.remove(this.currentElement);
        }
    }

}
