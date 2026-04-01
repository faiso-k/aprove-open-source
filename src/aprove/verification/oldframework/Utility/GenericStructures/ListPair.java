package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

public class ListPair<E> extends Pair<E, E> implements List<E> {

    private static final long serialVersionUID = 1L;

    public ListPair(final E key, final E value) {
        super(key, value);
    }

    @Override
    public int size() {
        return 2;
    }

    @Override
    public boolean isEmpty() {
        return false;
    }

    @Override
    public boolean contains(final Object o) {
        if (this.x == o || this.y == o) {
            return true;
        }
        if (this.x == null) {
            if (this.y == null) {
                return false;
            }
            return this.y.equals(o);
        }
        if (this.x.equals(o)) {
            return true;
        }
        if (this.y == null) {
            return false;
        }
        return this.y.equals(o);
    }

    @Override
    public Iterator<E> iterator() {
        return new Iterator<E>() {
            private int pos = 0;
            @Override
            public boolean hasNext() {
                return this.pos < 2;
            }
            @Override
            public E next() {
                switch (this.pos) {
                case 0:
                    this.pos++;
                    return ListPair.this.x;
                case 1:
                    this.pos++;
                    return ListPair.this.y;
                default:
                    throw new NoSuchElementException();
                }
            }
            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }
        };
    }

    @Override
    public Object[] toArray() {
        final Object[] b = new Object[2];
        b[0] = this.x;
        b[1] = this.y;
        return b;
    }

    @Override
    public <T> T[] toArray(final T[] a) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean add(final E e) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean remove(final Object o) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean containsAll(final Collection<?> c) {
        for (final Object o : c) {
            if (!this.contains(o)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public boolean addAll(final Collection<? extends E> c) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean removeAll(final Collection<?> c) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean retainAll(final Collection<?> c) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void clear() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean addAll(final int index, final Collection<? extends E> c) {
        throw new UnsupportedOperationException();
    }

    @Override
    public E get(final int index) {
        switch (index) {
        case 0:
            return this.x;
        case 1:
            return this.y;
        default:
            throw new IndexOutOfBoundsException(Integer.toString(index));
        }
    }

    @Override
    public E set(final int index, final E element) {
        E result;
        switch (index) {
        case 0:
            result = this.x;
            this.x = element;
            break;
        case 1:
            result = this.y;
            this.y = element;
            break;
        default:
            throw new IndexOutOfBoundsException(Integer.toString(index));
        }
        return result;
    }

    @Override
    public void add(final int index, final E element) {
        throw new UnsupportedOperationException();
    }

    @Override
    public E remove(final int index) {
        throw new UnsupportedOperationException();
    }

    @Override
    public int indexOf(final Object o) {
        if (this.x == o) {
            return 0;
        }
        if (this.x != null) {
            if (this.x.equals(o)) {
                return 0;
            }
        }
        if (this.y == o) {
            return 1;
        }
        if (this.y != null) {
            if (this.y.equals(o)) {
                return 1;
            }
        }
        return -1;
    }

    @Override
    public int lastIndexOf(final Object o) {
        if (this.y == o) {
            return 1;
        }
        if (this.y != null) {
            if (this.y.equals(o)) {
                return 1;
            }
        }
        if (this.x == o) {
            return 0;
        }
        if (this.x != null) {
            if (this.x.equals(o)) {
                return 0;
            }
        }
        return -1;
    }

    @Override
    public ListIterator<E> listIterator() {
        return new ListIterator<E>() {
            private int pos = 0;
            @Override
            public boolean hasNext() {
                return this.pos < 2;
            }
            @Override
            public E next() {
                switch (this.pos) {
                case 0:
                    this.pos++;
                    return ListPair.this.x;
                case 1:
                    this.pos++;
                    return ListPair.this.y;
                default:
                    throw new NoSuchElementException();
                }
            }
            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }
            @Override
            public boolean hasPrevious() {
                return this.pos > 0;
            }

            @Override
            public E previous() {
                switch (this.pos) {
                case 1:
                    this.pos--;
                    return ListPair.this.x;
                case 2:
                    this.pos--;
                    return ListPair.this.y;
                default:
                    throw new NoSuchElementException();
                }
            }

            @Override
            public int nextIndex() {
                switch (this.pos) {
                case 0:
                    return 0;
                case 1:
                    return 1;
                case 2:
                    return 2;
                default:
                    throw new IllegalStateException();
                }
            }

            @Override
            public int previousIndex() {
                switch (this.pos) {
                case 0:
                    return -1;
                case 1:
                    return 0;
                case 2:
                    return 1;
                default:
                    throw new IllegalStateException();
                }
            }
            @Override
            public void set(final E e) {
                switch (this.pos) {
                case 0:
                    ListPair.this.x = e;
                    break;
                case 1:
                    ListPair.this.y = e;
                    break;
                default:
                    throw new IllegalStateException();
                }
            }
            @Override
            public void add(final E e) {
                throw new UnsupportedOperationException();
            }
        };
    }

    @Override
    public ListIterator<E> listIterator(final int index) {
        throw new UnsupportedOperationException();
    }

    @Override
    public List<E> subList(final int fromIndex, final int toIndex) {
        throw new UnsupportedOperationException();
    }

}
