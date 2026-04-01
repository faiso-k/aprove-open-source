package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

/**
 * Utility functions for processing objects.
 * @author cryingshadow
 * @version $Id$
 */
public abstract class ObjectUtils {

    /**
     * A fold connects the specified start object with the specified input objects using the specified connector object
     * and the specified combinator. If the connector is c, the start object is e, and the input contains the objects
     * i1, i2, and i3, then the result is (i3 c (i2 c (i1 c e))).
     * @param input The input objects.
     * @param empty The start object.
     * @param connector The connector object.
     * @param combinator The combinator.
     * @return The folding of the input objects according to the specified combinator and start object.
     */
    public static <I, C, O> O binaryFold(Iterable<? extends I> input, O empty, C connector, Combinator<I, O, C, O> combinator) {
        O res = empty;
        for (I i : input) {
            res = combinator.combine(connector, i, res);
        }
        return res;
    }

    /**
     * Appends the folding of the specified input objects using the specified connector String to a String to the
     * specified StringBuilder. If the connector String is c and the input objects are i1, i2, and i3, then this
     * method appends &lt;i1&gt;c&lt;i2&gt;c&lt;i3&gt; to the specified StringBuilder where &lt;i&gt; is the result of
     * the toString() method on the object i. If the input objects contain only one element, only the result of calling
     * toString() on this element is appended. If the input objects are empty, this method does nothing.
     * @param input The input objects.
     * @param connector The connector String.
     * @param res The StringBuilder to append the folding to.
     */
    public static <I> void binaryStringFold(Iterable<I> input, String connector, StringBuilder res) {
        Iterator<I> it = input.iterator();
        while (it.hasNext()) {
            res.append(it.next());
            if (it.hasNext()) {
                res.append(connector);
            }
        }
    }

    /**
     * No instances.
     */
    private ObjectUtils() {
        // do not instantiate me
    }

}
