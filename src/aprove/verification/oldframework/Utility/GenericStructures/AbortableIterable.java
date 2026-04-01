package aprove.verification.oldframework.Utility.GenericStructures;

/**
 * this is like the default Iterable interface
 * with the difference that one gets Abortable Iterators
 * @author thiemann
 */
public interface AbortableIterable<T> {

    public AbortableIterator<T> iterator();

}