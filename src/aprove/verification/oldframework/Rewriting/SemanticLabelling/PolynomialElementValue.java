package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.util.*;

/**
 * Implementation of <code>ElementValue</code>, to be used by
 * <code>PolynomialFunctionRepresentation</code>.
 *
 * @author <a href="mailto:chang@ariadne.informatik.rwth-aachen.de">Christian Hang</a>
 * @version 1.0
 */
public class PolynomialElementValue implements ElementValue {

    /**
     * And as the real value modulo the carrierSetSize;
     */
    private int modValue;

    /**
     * the carrier set size
     */
    private int carrierSetSize;

    /**
     * Creates a new <code>PolynomialElementValue</code> instance from
     * an integer.
     *
     * @param integer the <code>int</code> to be represented by this
     * element.
     */
    public PolynomialElementValue(int integer, int carrierSetSize) {

    this.modValue = integer % carrierSetSize;
        if (this.modValue < 0) {
            this.modValue += carrierSetSize;
        }
        this.carrierSetSize = carrierSetSize;

    }


    @Override
    public int getIntValue() {

    return this.modValue;

    }

    @Override
    public boolean equalTo(ElementValue value) {

    return this.equals(value);

    }

    @Override
    public PolynomialElementValue decrement() {
        if (this.modValue == 0) {
            return null;
        } else {
            return new PolynomialElementValue(this.modValue-1, this.carrierSetSize);
        }
    }

    @Override
    public boolean greaterEqualTo(ElementValue value) {

    if (this.modValue >= value.getIntValue()) {
        return true;
    }
    return false;

    }

    @Override
    public boolean greaterThan(ElementValue value) {

    if (this.getIntValue() > value.getIntValue()) {
        return true;
    }
    return false;

    }

    @Override
    public String getLabel() {

    String label = "" + this.getIntValue();
    return label;

    }

    /**
     * Determines if this element is equal to another
     * <code>Object</code>. The semantics are the same as the {@link
     * #equalTo} method.
     *
     * @param obj an <code>Object</code> value to test for equality
     * @return <code>true</code> if <code>obj</code> is an instance of
     * <code>PolynomialElementValue</code> and represents the same
     * value as this object
     */
    @Override
    public boolean equals(Object obj) {

    if (obj instanceof PolynomialElementValue) {
        PolynomialElementValue value = (PolynomialElementValue) obj;
        if (this.modValue == value.modValue) {
        return true;
        }
    }
    return false;

    }

    @Override
    public int hashCode() {

    return this.modValue;

    }

    /**
     * Overwrites the <code>toString</code> method of
     * <code>Object</code>
     *
     * @return a <code>String</code> representing this element.
     */
    @Override
    public String toString() {

    String res = "" + this.modValue;
    return res;

    }

    public Iterator<List<ElementValue>> getElementListIterator(int arity) {

    return new ElementListIterator(arity);

    }

    @Override
    public Iterator<ElementValue> getElementIterator() {

    return new SimpleElementValueIterator();

    }

    @Override
    public boolean isListGreaterThan(List<ElementValue> left, List<ElementValue> right) {

    int leftValue = this.getListIntValue(left);
    int rightValue = this.getListIntValue(right);

    return (leftValue > rightValue);

    }

    private int getListIntValue(List<ElementValue> list) {

    int value = 0;
    int counter = 0;
    Iterator iter = list.iterator();
    while (iter.hasNext()) {
        value += ((ElementValue) iter.next()).getIntValue() * Math.pow(this.carrierSetSize, counter);
        counter++;
    }

    return value;

    }

    private class SimpleElementValueIterator implements Iterator<ElementValue> {
        private int currentSize = 0;
        @Override
        public boolean hasNext() {
            return this.currentSize != PolynomialElementValue.this.carrierSetSize;
        }
        @Override
        public ElementValue next() {
            if (this.hasNext()) {
                ElementValue res = new PolynomialElementValue(this.currentSize, PolynomialElementValue.this.carrierSetSize);
                this.currentSize++;
                return res;
            } else {
                throw new NoSuchElementException();
            }
        }
        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

    private class ElementListIterator implements Iterator<List<ElementValue>> {

    ElementVectorIterator iter;

    private ElementListIterator(int arity) {

        this.iter = new ElementVectorIterator(arity, PolynomialElementValue.this.carrierSetSize);

    }

    @Override
    public boolean hasNext() {

        return this.iter.hasNext();

    }

    @Override
    public List<ElementValue> next() {

        List<ElementValue> list = new ArrayList<ElementValue>();
        int[] vector = (int[]) this.iter.next();

        for (int idx = 0; idx < vector.length; idx++) {
        list.add(new PolynomialElementValue(vector[idx], PolynomialElementValue.this.carrierSetSize));
        }

        return list;

    }

    /**
     * This method is not implemented
     *
     */
    @Override
    public void remove() {
            throw new UnsupportedOperationException();
    }

    }
}
