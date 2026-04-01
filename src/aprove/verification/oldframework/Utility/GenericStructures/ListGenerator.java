package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

/**
 * a list generator uses a list [s_1,dots,s_n] of iterables, e.g. sets
 * and then generates the lists { [a_1,dots,a_n] | a_i in s_i for all i }.
 *
 * @author thiemann
 *
 */
public class ListGenerator<T> implements Iterator<List<T>> {

    final Iterable<T>[] iterables;
    final Iterator<T>[] iterators;
    final int n;
    boolean nextValid;
    ArrayList<T> workingList;
    int position;
    final boolean copy;

    /**
     *
     * @param iterables
     * @param getCopies if true, then the resulting List can be modified as wished. If false,
     *  then they may not be modified and moreover, by the next call to hasNext() or next() the previously
     *  returned list is modified. Note that true case is less efficient.
     */
    public ListGenerator(final Collection<? extends Iterable<T>> iterables, final boolean getCopies) {
        this.n = iterables.size();
        final Iterable<T>[] itbles = new Iterable[this.n];
        this.iterables = iterables.toArray(itbles);
        this.iterators = new Iterator[this.n];
        this.nextValid = false;
        this.workingList = new ArrayList<T>(this.n);
        this.copy = getCopies;
        this.position = 0;
    }

    @Override
    public boolean hasNext() {
        if (!this.nextValid) {
            this.computeNext();
        }
        return this.workingList != null;
    }

    @Override
    public ArrayList<T> next() {
        if (!this.hasNext()) {
            throw new NoSuchElementException();
        } else {
            this.nextValid = false;
            return this.copy ? new ArrayList<T>(this.workingList) : this.workingList;
        }
    }

    private void computeNext() {
        this.nextValid = true;
        while (this.position != -1) {
            // have we reached the end
            if (this.position == this.n) {
                this.position--;
                return;
            } else {
                Iterator<T> i = this.iterators[this.position];
                if (i == null) {
                    i = this.iterables[this.position].iterator();
                    if (i.hasNext()) {
                        this.workingList.add(i.next());
                    } else {
                        // no elements for current position
                        this.workingList = null;
                        return;
                    }
                    this.iterators[this.position] = i;
                    this.position++;
                } else {
                    if (i.hasNext()) {
                        this.workingList.set(this.position, i.next());
                        this.position++;
                    } else {
                        this.workingList.remove(this.position);
                        this.iterators[this.position] = null;
                        this.position--;
                    }
                }
            }
        }
        this.workingList = null;
    }

    @Override
    public void remove() {
        throw new UnsupportedOperationException();
    }

}
