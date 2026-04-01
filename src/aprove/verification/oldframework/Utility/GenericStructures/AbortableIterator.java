package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

import aprove.strategies.Abortions.*;

/**
 * An Abortable Iterator is like the standard Iterator with
 * the following differences:
 *
 * - all operations can be aborted due to time-outs
 * - remove is not supported (but this may be changed)
 *
 * @author thiemann
 */
public interface AbortableIterator<T> {

    public boolean hasNext(Abortion aborter) throws AbortionException;
    public T next(Abortion aborter) throws AbortionException, NoSuchElementException;

}