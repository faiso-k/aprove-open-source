package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

import aprove.*;

/**
 * an efficient array based implementation of a list. Note that unlike
 * usual lists add(0,.) and remove(0) are O(1)-operations, whereas
 * add(.) and remove(size-1) are O(n) operations.
 * (The internal array has reversed indices to the logical array to the
 * user).
 *
 * The Collection supports null-entries, but no method which requires comparing objects.
 *
 * The class is not at all synchronized or safe against ConcurrentModifications.
 * Even IndexOutOfBounds-Exception are not thrown (if one disabled assertions).
 * However, therefore this class is very performant and can be easily used for a
 * todoList.
 *
 * Up to now, not everything is implemented, e.g. equality, insertion/deletion
 * with arbitrary index which involves shifting.
 *
 * @author thiemann
 *
 * @param <T>
 */
public class ArrayStack<T> implements List<T> {

    private Object[] elements;
    private int size;

    public ArrayStack() {
        this(10);
    }

    public ArrayStack(int initialSize) {
        this.elements = new Object[initialSize];
        this.size = 0;
    }


    /*
    public ArrayStack(Collection<T> collection) {
        this.elements = collection.toArray();
        this.size = this.elements.length;
    }
    */

    public ArrayStack(ArrayStack<T> stack) {
        this.size = stack.size;
        this.elements = new Object[this.size];
        System.arraycopy(stack.elements, 0, this.elements, 0, this.size);
    }




    @Override
    public int size() {
        return this.size;
    }

    @Override
    public boolean isEmpty() {
        return this.size == 0;
    }

    @Override
    public boolean contains(Object o) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Iterator<T> iterator() {
        return new MyIterator(this.size);
    }

    @Override
    public Object[] toArray() {
        int n = this.size;
        Object[] a = new Object[n];
        int i = 0;
        while (n > 0) {
            n--;
            a[i] = this.elements[n];
            i++;
        }
        return a;
    }

    @Override
    public <T> T[] toArray(T[] a) {
        throw new UnsupportedOperationException();
    }

    /**
     * inserts at the end of the list / bottom of the stack. Costs O(n).
     * @param o
     * @return
     */
    @Override
    public boolean add(T o) {
        this.add(this.size, o);
        return true;
    }

    /**
     * inserts at the beginning of the list / top of the stack. Costs O(1).
     * @param o
     */
    public void push(T o) {
        this.ensureCapacity(this.size+1, true);
        this.elements[this.size] = o;
        this.size++;
    }

    /**
     * returns the beginning of the list / top of the stack. Costs O(1).
     * @param o
     */
    public T peek() {
        return (T) this.elements[this.size - 1];
    }

    /**
     * returns the and removes the beginning of the list / top of the stack. Costs O(1).
     * @param o
     */
    public T pop() {
        this.size--;
        T res = (T) this.elements[this.size];
        this.elements[this.size] = null; // for garbage collection
        return res;
    }

    /**
     * ensures that the stack has at least the given size. If you want to add many elements,
     * then it is more performant to increase directly to the final size, instead doing it
     * many times.
     * @param size
     */
    public void ensureCapacity(int size) {
        this.ensureCapacity(size, false);
    }

    private void ensureCapacity(int size, boolean increaseMoreThanNecessary) {
        if (this.elements.length < size) {
            Object[] newArray = new Object[increaseMoreThanNecessary ? size * 2 + 3 : size];
            System.arraycopy(this.elements, 0, newArray, 0, this.size);
            this.elements = newArray;
        }
    }

    @Override
    public boolean remove(Object o) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean containsAll(Collection<?> c) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean addAll(Collection<? extends T> c) {
        int n = c.size();
        if (n == 0) {
            return false;
        } else {
            int newLength = this.elements.length;
            int newSize = n + this.size;
            if (newLength < newSize) {
                newLength = newSize;
            }
            Object[] newObjects = new Object[newLength];
            System.arraycopy(this.elements, 0, newObjects, n, this.size);
            for (Object elem : c) {
                n--;
                newObjects[n] = elem;
            }
            if (Globals.useAssertions) {
                assert(n == 0);
            }
            this.size = newSize;
            this.elements = newObjects;
            return true;
        }
    }

    @Override
    public boolean addAll(int index, Collection<? extends T> c) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean retainAll(Collection<?> c) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void clear() {
        for (int i=0; i<this.size; i++) { // for garbage collection
            this.elements[i] = null;
        }
        this.size = 0;
    }

    @Override
    public T get(int index) {
        if (Globals.useAssertions) {
            assert(index < this.size && index >= 0);
        }
        index = this.size - index - 1;
        return (T) this.elements[index];
    }

    @Override
    public T set(int index, T element) {
        if (Globals.useAssertions) {
            assert(index < this.size && index >= 0);
        }
        index = this.size - index - 1;
        T prev = (T) this.elements[index];
        this.elements[index] = element;
        return prev;
    }

    @Override
    public void add(int index, T element) {
        if (index == 0) {
            this.ensureCapacity(this.size+1, true);
            this.elements[this.size] = element;
            this.size++;
        } else {
            throw new UnsupportedOperationException();
        }
    }

    @Override
    public T remove(int index) {
        if (Globals.useAssertions) {
            assert(index >= 0 && index < this.size);
        }
        if (index == 0) {
            this.size--;
            T res = (T) this.elements[this.size];
            this.elements[this.size] = null; // for garbarge collection
            return res;
        } else {
            throw new UnsupportedOperationException();
        }
    }

    @Override
    public int indexOf(Object o) {
        throw new UnsupportedOperationException();
    }

    @Override
    public int lastIndexOf(Object o) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ListIterator<T> listIterator() {
        return new MyIterator(this.size);
    }

    @Override
    public ListIterator<T> listIterator(int index) {
        if (Globals.useAssertions) {
            assert(index >= 0 && index <= this.size);
        }
        index = this.size - index;
        return new MyIterator(index);
    }

    @Override
    public List<T> subList(int fromIndex, int toIndex) {
        throw new UnsupportedOperationException();
    }

    private class MyIterator implements ListIterator<T> {


        private MyIterator(int index) {
            this.index = index;
        }

        private int index;         // the internal index
        private int lastIndex = -1; // the index of the element returned last

        @Override
        public boolean hasNext() {
            return this.index != 0;
        }

        @Override
        public T next() {
            if (Globals.useAssertions) {
                assert(this.index != 0);
            }
            this.index--;
            this.lastIndex = this.index;
            T elem = (T) ArrayStack.this.elements[this.index];
            return elem;
        }

        @Override
        public boolean hasPrevious() {
            return this.index != ArrayStack.this.size;
        }

        @Override
        public T previous() {
            if (Globals.useAssertions) {
                assert(this.index != ArrayStack.this.size);
            }
            this.lastIndex = this.index;
            T elem = (T) ArrayStack.this.elements[this.index];
            this.index++;
            return elem;
        }

        @Override
        public int nextIndex() {
            return ArrayStack.this.size - this.index;
        }

        @Override
        public int previousIndex() {
            return ArrayStack.this.size - this.index - 1;
        }

        @Override
        public void remove() {
            if (Globals.useAssertions) {
                assert(this.lastIndex != -1);
            }
            if (this.lastIndex == ArrayStack.this.size-1) {
                ArrayStack.this.size--;
                ArrayStack.this.elements[this.lastIndex] = null;
                this.lastIndex = -1;
                this.index = ArrayStack.this.size;
            } else {
                throw new UnsupportedOperationException();
            }
        }

        @Override
        public void set(T o) {
            if (Globals.useAssertions) {
                assert(this.lastIndex != -1);
            }
            ArrayStack.this.elements[this.lastIndex] = o;
        }

        @Override
        public void add(T o) {
            throw new UnsupportedOperationException();
        }

    }

    @Override
    public String toString() {
        String res = null;
        for (Object elem : this) {
            if (res == null) {
                res = "[" + elem;
            } else {
                res += ", " + elem;
            }
        }
        return res == null ? "[]" : res+"]";
    }

    @Override
    public boolean equals(Object o) {
        throw new RuntimeException("ArrayStacks do not support equality");
    }

    @Override
    public int hashCode() {
        throw new RuntimeException("ArrayStacks do not support equality");
    }



}
