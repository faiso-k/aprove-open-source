package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * @author Carsten Otto
 * @version 1.0
 */
public class BooleanTupleFunctionRepresentation
    implements FunctionRepresentation {

    /**
     * A <code>static</code> value for the size of the carrier set.
     */
    private final int carrierSetSize;

    /**
     * Create a new Function Representation for Boolean Tuples using the given
     * carrier set size (which determines the dimension of the tuples).
     * @param carrierSetSizeParam The size of the carrier set.
     */
    public BooleanTupleFunctionRepresentation(final int carrierSetSizeParam) {
        this.carrierSetSize = carrierSetSizeParam;
    }

    /**
     * @return the size of the carrier set.
     */
    @Override
    public int getCarrierSetSize() {
        return this.carrierSetSize;
    }

    /**
     * @return a new BooleanTupleElementValue of the same dimension as "this",
     * where the integer value determines the tuple (binary encoding).
     * @param value The value of the new BooleanTupleElementValue in binary
     * encoding.
     */
    @Override
    public ElementValue getElementValue(final int value) {
        return new BooleanTupleElementValue(value, this.carrierSetSize);
    }


    /**
     * For the current approach using boolean tuples the function representation
     * has no knowledge about the functions used to evaluate, so evaluation is
     * not possible here. Have a look at the labeller, which uses the SAT
     * formula to determine the functions used.
     * @return null
     * @param arguments not used.
     */
    @Override
    public ElementValue evaluate(final List<ElementValue> arguments) {
        assert (false) : "This is not possible.";
        return null;
    }

    /**
     * @return true iff the other object is a BooleanTupleFunctionRepresentation
     * for tuples of the same dimension.
     * @param obj the other object.
     */
    @Override
    public boolean equals(final Object obj) {
        if (obj != null && obj instanceof BooleanTupleFunctionRepresentation) {
            final BooleanTupleFunctionRepresentation btfr =
                (BooleanTupleFunctionRepresentation) obj;
            return (this.carrierSetSize == btfr.carrierSetSize);
        }
        return false;
    }

    /**
     * The hashcode is just the carrier set size, as no other useful value
     * exists.
     * @return the hashcode.
     */
    @Override
    public int hashCode() {
        return this.carrierSetSize;
    }

    /**
     * This method is not implemented, see "evaluate()".
     * @return false.
     * @param position not used.
     */
    @Override
    public boolean requiresArgument(final int position) {
        assert (false) : "This is not possible.";
        return false;
    }

    /**
     * @return all possible pairs of lists of BooleanTupleElementValues
     * where the list has size "arity" and for each pair of lists a, b it holds
     * a > b.
     * @param arity the arity of the returned element values.
     */
    @Override
    public List<ElementPair> getDecrElementPairs(final int arity) {
        final List<ElementPair> pairs = new ArrayList<ElementPair>();
        final BooleanTupleElementValue defaultValue =
            new BooleanTupleElementValue(0, this.carrierSetSize);

        // outer is an iterator over lists of size "arity". All lists that are
        // returned represent the possible combinations of "arity"
        // ElementValues. for arity 2, dimension 2: [[0,0],[0,0]] and
        // [[0,1],[0,0]] and ... are returned.
        final Iterator<List<ElementValue>> outer =
            defaultValue.getElementListIterator(arity);

        while (outer.hasNext()) {
            final List<ElementValue> outerValue = outer.next();
            for (int i = 0; i < arity; i++) {
                final List<ElementValue> innerValue =
                    new ArrayList<ElementValue>(outerValue);
                final BooleanTupleElementValue current =
                    (BooleanTupleElementValue) innerValue.get(i);
                final BooleanTupleElementIterator it =
                    new BooleanTupleElementIterator(current);
                while (it.hasNext()) {
                    final ElementValue previous = it.next();
                    if (!previous.equals(current)) {
                        innerValue.set(i, previous);
                        pairs.add(new ElementPair(outerValue, innerValue));
                    }
                }
            }
        }
        return pairs;

    }

    /**
     * @return An iterator that returns all lists smaller than the given one.
     * @param elementList The list to compare with.
     */
    @Override
    public Iterator<List<ElementValue>> getSmallerElements(
            final List<ElementValue> elementList
            ) {
        final List<Iterable<ElementValue>> smallers =
            new ArrayList<Iterable<ElementValue>>(elementList.size());

        for (final ElementValue e : elementList) {
            smallers.add(new Iterable<ElementValue>() {

                @Override
                public Iterator<ElementValue> iterator() {
                    return new BooleanTupleElementIterator(e);
                }
            });
        }

        final boolean copies = true;
        return new ListGenerator<ElementValue>(smallers, copies);
    }

    /**
     * iterates over all elements which are smaller or equal than the initial
     * element.
     */
    private static final class BooleanTupleElementIterator
        implements Iterator<ElementValue> {

        /**
         * Remember the initial (integer) value to compare with.
         */
        private final int initial;

        /**
         * This is the current element which will be returned next.
         */
        private BooleanTupleElementValue current;

        /**
         * Remember the starting element and prepare the first value to return.
         * @param init The initial element to compare with.
         */
        public BooleanTupleElementIterator(final ElementValue init) {
            assert (init instanceof BooleanTupleElementValue);
            this.initial = ((BooleanTupleElementValue) init).getIntValue();
            this.current = (BooleanTupleElementValue) init;
        }

        /**
         * @return true iff some smaller element exists.
         */
        @Override
        public boolean hasNext() {
            return this.current != null;
        }

        /**
         * @return the next element.
         */
        @Override
        public ElementValue next() {
            final BooleanTupleElementValue ret = this.current;

            // calculate new smaller EV
            final int currentIntValue = this.current.getIntValue();
            this.current = null;
            int decrIntValue = currentIntValue - 1;
            while (decrIntValue >= 0) {
                if ((this.initial | decrIntValue) <= this.initial) {
                    // some 1s now are 0s, but no new 1 appeared
                    final BooleanTupleElementValue ev =
                        new BooleanTupleElementValue(
                                decrIntValue, ret.getCarrierSetSize());
                    this.current = ev;
                    decrIntValue = -1; // end loop
                } else {
                    decrIntValue -= 1;
                }
            }
            return ret;
        }

        /**
         * Not implemented.
         */
        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }

    };

    /**
     * Not implemented, sea "evaluate()".
     * @return false;
     */
    @Override
    public boolean isWeaklyMonotonic() {
        assert (false) : "Why is this needed?";
        return false;
    }

    /**
     * Not implemented, sea "evaluate()".
     * @return "".
     */
    @Override
    public String toString() {
        assert (false) : "Why is this needed?";
        return "";
    }

    /**
     * Not implemented, sea "evaluate()".
     * @return null.
     * @param arity not used.
     * @param needMonotonic not used.
     */
    @Override
    public Iterator<FunctionRepresentation> getFunctionIterator(
            final int arity,
            final boolean needMonotonic) {
        assert (false) : "Why is this needed?";
        return null;
    }

    /**
     * Not implemented, see "evaluate()".
     * @return "".
     */
    public String toHTML() {
        assert (false) : "Why is this needed?";
        return "";
    }

    /**
     * @return a dummy FunctionRepresentation using the same carrier set.
     * This is useful for irrelevant function symbols that do not need some
     * specific label.
     * @param arity not used.
     */
    @Override
    public FunctionRepresentation getConstantRepresentation(final int arity) {
        return new BooleanTupleFunctionRepresentation(this.carrierSetSize);
    }

    /**
     * Not implemented, see "evaluate()".
     * @return "".
     * @param o not used.
     */
    @Override
    public String export(final Export_Util o) {
        assert (false) : "Why is this needed?";
        return "";
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        // Don't know if this really is NOT needed, but obviously it isn't right
        // at the moment
        assert (false) : "Why is this needed?";
        return null;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return CPFTag.notYetImplemented(doc, this);
    }

}
