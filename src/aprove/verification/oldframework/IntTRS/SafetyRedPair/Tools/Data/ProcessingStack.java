package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data;

import java.util.*;

/**
 * @author marinag
 * Utility class to manage a set of processed and to be processed items
 * @param <T>
 */
public class ProcessingStack<T> {
    Set<T> processed = new HashSet<>();
    Stack<T> toProcess = new Stack<>();

    public ProcessingStack() {
        this(new HashSet<T>());
    }

    public ProcessingStack(final Collection<T> init) {
        for (final T item : new HashSet<T>(init)) {
            this.push(item);
        }
    }


    public T push(final T item) {
        if (this.processed.contains(item)) {
            return item;
        }

        return this.toProcess.push(item);
    }

    public void pushAll(final Collection<T> items) {
        for (final T item : items) {
            this.push(item);
        }
    }

    public T pop() {
        final T item = this.toProcess.pop();
        this.processed.add(item);
        return item;
    }

    public boolean isEmpty() {
        return this.toProcess.isEmpty();
    }

    public Set<T> getProcessed() {
        return this.processed;
    }

    @Override
    public String toString() {
        return "TODO: " + this.toProcess.toString() + "\nDONE: " + this.processed.toString();
    }

}
