/*
 * Created on 12.04.2005
 */
package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

import aprove.strategies.Abortions.*;

/**
 * this class takes an iterator and stores the results in a
 * memory. Then every iterator produces by this class will use
 * the memory to obtain its elements. However, the memory will only
 * store those elements that have been requested.
 * This class IS THREAD SAFE.
 * @author thiemann
 */
public class MemoryAbortableIterable<A> implements AbortableIterable<A> {

    private AbortableIterator<A> iterator;
    private List<A> memory;


    public MemoryAbortableIterable(AbortableIterator<A> iterator) {
        this.iterator = iterator;
        this.memory = new ArrayList<A>();
    }

    @Override
    public AbortableIterator<A> iterator() {
        return new MemoryIterator();
    }

    public void shutdown() {
        this.iterator = null;
        this.memory = null;
    }

    private synchronized void computeNext(Abortion aborter) throws AbortionException {
        if (this.iterator.hasNext(aborter)) {
            this.memory.add(this.iterator.next(aborter));
        }
    }



    private class MemoryIterator implements AbortableIterator<A> {
        private int position;
        private A next;
        private boolean haveNext;
        private boolean nextValid;

        private MemoryIterator() {
            this.position = 0;
            this.nextValid = false;
        }

        private void computeNext(Abortion aborter) throws AbortionException {
            if (MemoryAbortableIterable.this.memory.size() > this.position) {
                this.next = MemoryAbortableIterable.this.memory.get(this.position);
                this.position++;
                this.haveNext = true;
            } else {
                MemoryAbortableIterable.this.computeNext(aborter);
                if (MemoryAbortableIterable.this.memory.size() > this.position) {
                    this.next = MemoryAbortableIterable.this.memory.get(this.position);
                    this.position++;
                    this.haveNext = true;
                } else {
                    this.haveNext = false;
                    this.next = null;
                }
            }
            this.nextValid = true;
        }


        @Override
        public boolean hasNext(Abortion aborter) throws AbortionException {
            synchronized(MemoryAbortableIterable.this.iterator) {
                if (!this.nextValid) {
                    this.computeNext(aborter);
                }
                return this.haveNext;
            }
        }

        @Override
        public A next(Abortion aborter) throws AbortionException {
            synchronized(MemoryAbortableIterable.this.iterator) {
                if (!this.hasNext(aborter)) {
                    throw new NoSuchElementException();
                } else {
                    this.nextValid = false;
                    return this.next;
                }
            }
        }


    }

}
