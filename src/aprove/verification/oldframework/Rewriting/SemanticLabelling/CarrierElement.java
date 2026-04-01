package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.util.*;

import aprove.*;
import immutables.*;

public class CarrierElement {

    private final ImmutablePair<Integer, Integer> element;
    private final int hashValue;
    private final int actValue;
    private final int cSS;

    public CarrierElement(final int value, final int carrier) {
        if (carrier == -1) {
            this.element = new ImmutablePair<Integer, Integer>(value, carrier);
            this.hashValue = value;
            this.actValue = value;
            this.cSS = carrier;
        } else {
            int modValue;
            modValue = (value % carrier);
            this.element = new ImmutablePair<Integer, Integer>(modValue, carrier);
            this.hashValue = modValue;
            this.actValue = modValue;
            this.cSS = carrier;
        }
    }

    @Override
    public boolean equals(final Object other) {
        if (other instanceof CarrierElement) {
            final CarrierElement otherPoly = (CarrierElement) other;
            return this.element.equals(otherPoly.element);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return this.hashValue;
    }

    /**
     *
     * @return the integer value as a String
     */
    public String getLabel() {
        final String label = "" + this.getIntValue();
        return label;
    }

    /**
     *
     * @return the intgeger value of the CarrierElement
     * in case the carrier is finite, the value is taken
     * modulo the carrier.
     */
    public int getIntValue() {
        return this.element.x;
    }

    /**
     * Checks if a CarrierElement has a successor.
     * <div style= "position: absolute; left: 8px; font-weight: bold;" > NOTE: </div><br>
     * in case the carrier is infinite the value is always true of course
     * @return true if the CarrierElement has a successor, false otherwise
     */
    public boolean elementHasSuccessor() {
        if (this.cSS == -1) {
            return true;
        } else {
            return (this.actValue < this.cSS);
        }

    }

    /**
     *
     * @return previous CarrierElement of this, <br>
     * <b>null</b> in case there doesn't exist a predecssor.
     */
    public CarrierElement decrement() {
        if (this.actValue != 0) {
            return new CarrierElement((this.actValue - 1), this.cSS);
        } else {
            return null;
        }
    }

    /**
     * When enabling assertions method checks also if
     * this and other have the same carrier.
     * @param other
     * @return true, if both have the same carrier and
     * value of this is bigger or equal to value of other.
     *      false if both have the same carrier and
     * value of this is not bigger or equal to value of other.
     * @throws RuntimeException if this and other have different carrier size.
     */
    public boolean greaterEqualTo(final CarrierElement other) {
        if (Globals.useAssertions) {
            if (this.cSS != other.cSS) {
                throw new RuntimeException("Elements are not compareable, they have a different carrier!");
            }
        }
        return (this.actValue >= other.actValue);
    }

    /**
     * When enabling assertions method checks also if
     * this and other have the same carrier.
     * @param other
     * @return true, if both have the same carrier and
     * value of this is bigger than value of other.
     *      false if both have the same carrier and
     * value of this is not bigger than value of other.
     * @throws RuntimeException if this and other have different carrier size.
     */
    public boolean greaterThan(final CarrierElement other) {
        if (Globals.useAssertions) {
            if (this.cSS != other.cSS) {
                throw new RuntimeException("Elements are not compareable, they have a different carrier!");
            }
        }
        return (this.actValue > other.actValue);
    }

    /**
     * @return an iterator over the CarrierElements <br>
     * <div style= "position: absolute; left: 8px; font-weight: bold;" > NOTE: </div><br>
     * in case the carrier is infinite hasNext() will always return true!
     */
    public Iterator<CarrierElement> getElementIterator() {
        return new CarrierElementIterator();
    }

    private class CarrierElementIterator implements Iterator<CarrierElement> {
        private int currentSize = 0;
        private int currentSizeAbsolutValue = 0;

        @Override
        public boolean hasNext() {
            if (this.currentSize < 0) {
                this.currentSizeAbsolutValue = (this.currentSize * (-1));
            } else {
                this.currentSizeAbsolutValue = this.currentSize;
            }
            return this.currentSizeAbsolutValue != CarrierElement.this.cSS;
        }

        @Override
        public CarrierElement next() {
            if (this.hasNext()) {
                final CarrierElement res = new CarrierElement(this.currentSize, CarrierElement.this.cSS);
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

}
