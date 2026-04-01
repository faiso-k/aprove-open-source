package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.util.*;

/**
 * @author Carsten Otto
 * @version 1.0
 */
public class BooleanTupleElementValue implements ElementValue {

    private class ElementListIterator implements Iterator<List<ElementValue>> {
        private final ElementVectorIterator iter;

        private ElementListIterator(final int arity) {
            this.iter = new ElementVectorIterator(arity, BooleanTupleElementValue.this.carrierSetSize);
        }

        @Override
        public boolean hasNext() {
            return this.iter.hasNext();
        }

        @Override
        public List<ElementValue> next() {
            final List<ElementValue> list = new ArrayList<ElementValue>();
            final int[] vector = this.iter.next();

            for (final int element : vector) {
                list.add(new BooleanTupleElementValue(element, BooleanTupleElementValue.this.carrierSetSize));
            }
            return list;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

    private class SimpleElementValueIterator implements Iterator<ElementValue> {
        private int currentSize = 0;

        @Override
        public boolean hasNext() {
            return this.currentSize != BooleanTupleElementValue.this.carrierSetSize;
        }

        @Override
        public ElementValue next() {
            if (this.hasNext()) {
                final ElementValue res =
                    new BooleanTupleElementValue(this.currentSize, BooleanTupleElementValue.this.carrierSetSize);
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

    private final int carrierSetSize;

    private final int dimension;

    private final int modValue;

    public BooleanTupleElementValue(final Boolean[] result, final int carrierSetSizeParam) {
        this.carrierSetSize = carrierSetSizeParam;
        this.dimension = result.length;
        int value = 0;
        for (int i = 0; i < result.length; i++) {
            if (result[i]) {
                value += (int) Math.pow(2, i);
            }
        }
        this.modValue = value;
    }

    public BooleanTupleElementValue(final int integer, final int carrierSetSizeParam) {
        this.carrierSetSize = carrierSetSizeParam;
        this.dimension = (int) (Math.log(carrierSetSizeParam) / Math.log(2));
        this.modValue = integer % this.carrierSetSize;
    }

    public BooleanTupleElementValue(final List<Boolean> result, final int carrierSetSizeParam) {
        this.carrierSetSize = carrierSetSizeParam;
        this.dimension = result.size();
        int value = 0;
        for (int i = 0; i < result.size(); i++) {
            if (result.get(i)) {
                value += (int) Math.pow(2, i);
            }
        }
        this.modValue = value;
    }

    @Override
    public BooleanTupleElementValue decrement() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(final Object obj) {
        if (obj instanceof BooleanTupleElementValue && obj != null) {
            final BooleanTupleElementValue value = (BooleanTupleElementValue) obj;
            if (this.modValue == value.modValue) {
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean equalTo(final ElementValue value) {
        return this.equals(value);
    }

    public List<Boolean> getBools() {
        final List<Boolean> result = new ArrayList<Boolean>(this.dimension);
        for (int i = 0; i < this.dimension; i++) {
            result.add(i, (this.modValue / (int) Math.pow(2, i)) % 2 == 1);
        }
        return result;
    }

    public int getCarrierSetSize() {
        return this.carrierSetSize;
    }

    @Override
    public Iterator<ElementValue> getElementIterator() {
        return new SimpleElementValueIterator();
    }

    public Iterator<List<ElementValue>> getElementListIterator(final int arity) {
        return new ElementListIterator(arity);
    }

    @Override
    public int getIntValue() {
        return this.modValue;
    }

    @Override
    public String getLabel() {
        String result = "[";
        for (int i = 0; i < this.dimension; i++) {
            result += (this.modValue / (int) Math.pow(2, i)) % 2 + ", ";
        }
        result = result.substring(0, result.length() - 2);
        return result + "]";
    }

    @Override
    public boolean greaterEqualTo(final ElementValue value) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean greaterThan(final ElementValue value) {
        throw new UnsupportedOperationException();
    }

    @Override
    public int hashCode() {
        return this.modValue;
    }

    @Override
    public boolean isListGreaterThan(final List<ElementValue> left, final List<ElementValue> right) {
        assert (false);
        final int leftValue = this.getListIntValue(left);
        final int rightValue = this.getListIntValue(right);
        return (leftValue > rightValue);
    }

    @Override
    public String toString() {
        return this.getLabel();
    }

    private int getListIntValue(final List<ElementValue> list) {
        assert (false);
        int value = 0;
        int counter = 0;
        final Iterator iter = list.iterator();
        while (iter.hasNext()) {
            value += ((ElementValue) iter.next()).getIntValue() * Math.pow(this.carrierSetSize, counter);
            counter++;
        }
        return value;
    }
}
