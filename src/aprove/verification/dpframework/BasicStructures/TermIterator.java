package aprove.verification.dpframework.BasicStructures;

import java.util.*;

/**
 * Iterating over a term, depth first.
 */
public class TermIterator implements Iterator<TermIterator.Entry> {

    private final Stack<TRSTerm> termStack;
    private final Stack<Position> posStack;

    public TermIterator(final TRSTerm t){
        this.termStack = new Stack<TRSTerm>();
        this.termStack.push(t);

        this.posStack = new Stack<Position>();
        this.posStack.push(Position.create());
    }

    @Override
    public boolean hasNext() {
        return !this.termStack.isEmpty();
    }

    @Override
    public Entry next() {
        final TRSTerm t = this.termStack.pop();
        final Position p = this.posStack.pop();
        if (!t.isVariable()) {
            final TRSFunctionApplication funapp = (TRSFunctionApplication) t;
            int size = funapp.getArguments().size();
            for (int i=0; i < size; i++) {
                this.termStack.push(funapp.getArgument(i));
                this.posStack.push(p.append(i));
            }
        }
        return new Entry(t,p);
    }

    @Override
    public void remove() {
        throw new UnsupportedOperationException();
    }

    public static class Entry {
        private final TRSTerm t;
        private final Position p;

        Entry(TRSTerm t, Position p) {
            this.t = t;
            this.p = p;
        }

        public TRSTerm getTerm() {
            return this.t;
        }

        public Position getPosition() {
            return this.p;
        }
    }
}