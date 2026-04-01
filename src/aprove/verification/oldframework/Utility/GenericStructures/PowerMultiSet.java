package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

public abstract class PowerMultiSet {

    /**
     * iterates nothing
     */
    private static final <T> Iterator<MultiSet<T>> THE_EMPTY_ITERATOR() {
        return new Iterator<MultiSet<T>>() {
            @Override
            public boolean hasNext() {
                return false;
            }
            @Override
            public MultiSet<T> next() {
                throw new NoSuchElementException();
            }
            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }
        };
    }

    /**
     * iterates the emptyset (empty collection) once
     */
    private static final <T> Iterator<MultiSet<T>> THE_EMPTYSET_ITERATOR() {
        return new Iterator<MultiSet<T>>() {

            private boolean notReturned = true;

            @Override
            public boolean hasNext() {
                return this.notReturned;
            }
            @Override
            public MultiSet<T> next() {
                if (this.notReturned) {
                    this.notReturned = false;
                    return new HashMultiSet<T>();
                } else {
                    throw new NoSuchElementException();
                }
            }
            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }
        };
    }

    /**
     * iterates the one element {theT, ..., theT} (size times theT),
     * after iteration adds theT to the baseSet
     * @param baseSet - should be the emptySet!
     * @param theT
     * @param size
     * @return
     */
    private static final <T> Iterator<MultiSet<T>> THE_SIZE_T_ITERATOR(final Collection<T> baseSet, final T theT, final int size) {
        return new Iterator<MultiSet<T>>() {
            boolean notReturned = true;
            boolean mustAdd = true;

            @Override
            public boolean hasNext() {
                if (this.notReturned) {
                    return true;
                } else {
                    if (this.mustAdd) {
                        this.mustAdd = false;
                        baseSet.add(theT);
                    }
                    return false;
                }
            }

            @Override
            public MultiSet<T> next() {
                if (this.notReturned) {
                    this.notReturned = false;
                    MultiSet<T> ms = new HashMultiSet<T>();
                    ms.add(theT, size);
                    return ms;
                } else {
                    throw new NoSuchElementException();
                }
            }

            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }

        };
    }

    /**
     * takes a nonEmpty set remSet and a T element theT and iterates over all
     * multisets of remSet cup {theT} of given size.
     * If all elements are iterated then remSet is changed to remSet cup {theT},
     * but there is no specified state in the meantime
     * @param remSet
     * @param theT
     * @param size
     * @return
     */
    private static final <T> Iterator<MultiSet<T>> THE_RECURSIVE_T_ITERATOR(final Collection<T> remSet, final T theT, final int size) {

        return new Iterator<MultiSet<T>>() {
            boolean nextValid = false;
            MultiSet<T> nextMs = null;
            int takeSize = size+1;
            Iterator<MultiSet<T>> it = null;

            private void computeNext() {
                if (!this.nextValid) {
                    this.nextMs = null;
                    while (this.nextMs == null) {
                        if (this.it == null) {
                            if (this.takeSize > 0) {
                                this.takeSize--;
                                this.it = PowerMultiSet.THE_EXACT_SIZE_ITERATOR(remSet, size-this.takeSize);
                            } else {
                                remSet.add(theT);
                                break;
                            }
                        } else {
                            if (this.it.hasNext()) {
                                this.nextMs = this.it.next();
                                this.nextMs.add(theT, this.takeSize);
                            } else {
                                this.it = null;
                            }
                        }
                    }
                    this.nextValid = true;
                }
            }

            @Override
            public boolean hasNext() {
                this.computeNext();
                return this.nextMs != null;
            }

            @Override
            public MultiSet<T> next() {
                if (this.hasNext()) {
                    this.nextValid = false;
                    MultiSet<T> res = this.nextMs;
                    return res;
                } else {
                    throw new NoSuchElementException();
                }
            }

            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }

        };
    }

    /**
     * during the iteration process the set will be modified,
     * however, after complete iteration, the set should be unchanged;
     * Iterates over all multisets up to given size.
     * @param baseSet
     * @param size a value >= 0
     * @return
     */
    private static final <T> Iterator<MultiSet<T>> THE_UP_TO_SIZE_ITERATOR(final Collection<T> baseSet, final int size) {

        return new Iterator<MultiSet<T>>() {
            boolean nextValid = false;
            MultiSet<T> nextMs = null;
            int currSize = -1;
            Iterator<MultiSet<T>> it = null;

            private void computeNext() {
                if (!this.nextValid) {
                    this.nextMs = null;
                    while (this.nextMs == null) {
                        if (this.it == null) {
                            if (this.currSize < size) {
                                this.currSize++;
                                this.it = PowerMultiSet.THE_EXACT_SIZE_ITERATOR(baseSet, this.currSize);
                            } else {
                                break;
                            }
                        } else {
                            if (this.it.hasNext()) {
                                this.nextMs = this.it.next();
                            } else {
                                this.it = null;
                            }
                        }
                    }
                    this.nextValid = true;
                }
            }

            @Override
            public boolean hasNext() {
                this.computeNext();
                return this.nextMs != null;
            }

            @Override
            public MultiSet<T> next() {
                if (this.hasNext()) {
                    this.nextValid = false;
                    MultiSet<T> res = this.nextMs;
                    return res;
                } else {
                    throw new NoSuchElementException();
                }
            }

            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }

        };
    }



    /**
     * during the iteration process the set will be modified,
     * however, after complete iteration, the set should be unchanged;
     * Iterates over all multisets of exactly the given size.
     * @param baseSet
     * @param size a value >= 0
     * @return
     */
    private static final <T> Iterator<MultiSet<T>> THE_EXACT_SIZE_ITERATOR(Collection<T> baseSet, int size) {

        if (size == 0) {
            return PowerMultiSet.THE_EMPTYSET_ITERATOR();
        } else {
            Iterator<T> i = baseSet.iterator();
            if (i.hasNext()) {
                T theT = i.next();
                i.remove();
                if (i.hasNext()) {
                    return PowerMultiSet.THE_RECURSIVE_T_ITERATOR(baseSet, theT, size);
                } else {
                    return PowerMultiSet.THE_SIZE_T_ITERATOR(baseSet, theT, size);
                }
            } else {
                return PowerMultiSet.THE_EMPTY_ITERATOR();
            }
        }
    }

    /**
     * creates an iterable over multisets over the baseSet.
     * The returned multisets may be modified.
     * If exactSize is true, then all multisets over the given size will be produced.
     * Otherwise, all multisets up to size will be produced, starting with small ones.
     * Safe, but overhead of one set-copy per iterator()-call.
     * @param baseSet
     * @param size
     * @param exactSize
     * @return
     */
    public static final <T> Iterable<MultiSet<T>> create(final Set<T> baseSet, final int size, final boolean exactSize) {
        return new Iterable<MultiSet<T>>() {

            @Override
            public Iterator<MultiSet<T>> iterator() {
                Collection<T> copy = new LinkedList<T>(baseSet);
                if (exactSize) {
                    return PowerMultiSet.THE_EXACT_SIZE_ITERATOR(copy, size);
                } else {
                    return PowerMultiSet.THE_UP_TO_SIZE_ITERATOR(copy, size);
                }
            }

        };
    }

    /**
     * creates an iterable over multisets over the baseSet.
     * If exactSize is true, then all multisets over the given size will be produced.
     * Otherwise, all multisets up to size will be produced, starting with small ones.
     * The returned multisets may be modified.
     *
     * There is no overhead in set-copies as in create. However,
     * the baseSet will be changed during iteration, but after all elements
     * have been iterated, the baseSet will have its original state (but perhaps in different order).
     * Moreover, it is not allowed to create a second iterator until the first has completely iterated
     * because of the same reason that the set is changed during processing.
     * @param baseSet
     * @param size
     * @param exactSize
     * @return
     */
    public static final <T> Iterable<MultiSet<T>> createDestructively(final Set<T> baseSet, final int size, final boolean exactSize) {
        return new Iterable<MultiSet<T>>() {
            @Override
            public Iterator<MultiSet<T>> iterator() {
                if (exactSize) {
                    return PowerMultiSet.THE_EXACT_SIZE_ITERATOR(baseSet, size);
                } else {
                    return PowerMultiSet.THE_UP_TO_SIZE_ITERATOR(baseSet, size);
                }
            }

        };
    }


}
