package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.util.*;

/**
 * This interface models an element in the carrier set of {@link
 * Model}. It also provides general methods to work with the carrier
 * set. All implementations must provide a mapping from an element to
 * an integer, although all Semantic-Labelling classes use abstract
 * representations of functions and elements and do not rely on
 * integers as a basis. Each {@link FunctionRepresentation} should
 * have its own implementation of <code>ElementValue</code>
 *
 * @author <a href="mailto:chang@ariadne.informatik.rwth-aachen.de">Christian Hang</a>
 * @version 1.0
 */
public interface ElementValue {

    /**
     * Determines if another <code>ElementValue</code> represents the
     * same value as this object.
     *
     * @param value another <code>ElementValue</code> to check against
     * @return <code>true</code> if the two values should be
     * considered equal, <code>false</code> otherwise
     */
    public boolean equalTo(ElementValue value);

    /**
     * returns an element which is exactly below the this value.
     * If this element is the least value, then null is returned.
     * @return
     */
    public ElementValue decrement();

    /**
     * Determines if this object should be considered greater or equal
     * to the value represented by another <code>ElementValue</code>.
     *
     * @return <code>true</code> if the two elements are comparable
     * and this object should be considered greater or equal to
     * <code>value</code>, <code>false</code> otherwise.
     */
    public boolean greaterEqualTo(ElementValue value);

    /**
     * Determines if this object should be considered greater than
     * than the value represented by another <code>ElementValue</code>.
     *
     * @return <code>true</code> if the two elements are comparable
     * and this object should be considered greater than
     * <code>value</code>, <code>false</code> otherwise.
     */
    public boolean greaterThan(ElementValue value);

    /**
     * Gets an appropriate integer representation of this object,
     * taking into consideration the size of the carrier set. It is
     * preferred to use {@link #equalTo} and {@link #greaterEqualTo}
     * instead of this method, to determine the relation between two
     * elements.
     *
     * @return an <code>int</code> representation of this value
     */
    public int getIntValue();

    /**
     * Gets a <code>String</code>, that is probably shorter than the
     * one returned by <code>toString</code> and can be used to label a
     * <code>FunctionSymbol</code>
     *
     * @return a <code>String</code> that can be used as a label
     */
    public String getLabel();

    /**
     * Gets an <code>Iterator</code> over all possible elements of the
     * carrier set. The implementation is responsible to return them
     * in a meaningful way, preferrably starting with the lowest and
     * continuing in increasing order.
     *
     * @return an <code>Iterator</code> over all possible
     * <code>ElementValue</code>s
     */
    public Iterator<ElementValue> getElementIterator();

    public boolean isListGreaterThan(List<ElementValue> left, List<ElementValue> right);

}
