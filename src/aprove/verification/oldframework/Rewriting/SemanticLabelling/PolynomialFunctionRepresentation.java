package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * Implementation of <code>FunctionRepresentation</code>, that uses
 * <code>Polynomial</code>s, to represent the functions internally.
 *
 * @author <a href="mailto:chang@ariadne.informatik.rwth-aachen.de">Christian Hang</a>
 * @version 1.0
 */
@SuppressWarnings("serial")
public class PolynomialFunctionRepresentation implements FunctionRepresentation, java.io.Serializable {
    /**
     * A <code>static</code> value for the size of the carrier set
     */
    private int carrierSetSize;

    private final YNM[] requiresArgument;

    /**
     * The interal representation of the function. The arguments of
     * the function are represented by variables in the polynomial,
     * named "x_n", where "n" is the zero-based argument position
     */
    private final Polynomial poly;

    /**
     * Creates a new <code>PolynomialFunctionRepresentation</code>
     * instance, that is marked irrelevant.
     *
     */
    public PolynomialFunctionRepresentation(final int carrierSetSize) {

    this(null, carrierSetSize, 0);

    }

    /**
     * Creates a new <code>PolynomialFunctionRepresentation</code>
     * instance, that represents the function defined by the
     * <code>Polynomial</code>
     *
     * @param poly a <code>Polynomial</code> representing the
     * function. If this argument is <code>null</code>, an irrelevant
     * function will be instantiated.
     */
    public PolynomialFunctionRepresentation(final Polynomial poly, final int carrierSetSize, final int arity) {

    this.poly = poly;
    this.carrierSetSize = carrierSetSize;
        this.requiresArgument = new YNM[arity];
        Arrays.fill(this.requiresArgument, YNM.MAYBE);

    }

    /**
     * Sets the size of the carrier set.
     *
     * @param size new size of the carrier set. Shouldn't be called by
     * anyone except, the <code>SemanticLabellingSccProcessor</code>
     */
    public void setCarrierSetSize(final int size) {

    this.carrierSetSize = size;

    }

    @Override
    public int getCarrierSetSize() {

    return this.carrierSetSize;

    }


    @Override
    public ElementValue getElementValue(final int value) {

    return new PolynomialElementValue(value, this.carrierSetSize);

    }


    @Override
    public ElementValue evaluate(final List<ElementValue> arguments) {

    final HashMap<String, Integer> args = new HashMap<String, Integer>();
    int counter = 0;
    for (final ElementValue elem : arguments) {
        final PolynomialElementValue value = (PolynomialElementValue) elem;
        if (value != null) {
        args.put("x_" + counter, value.getIntValue());
        }
        counter++;
    }

    return new PolynomialElementValue((int) this.poly.evaluate(args), this.carrierSetSize);

    }

    /**
     * Determines if this <code>FunctionRepresentation</code> is equal
     * to another. That is the case, if they are both instances of
     * <code>PolynomialFunctionRepresentation</code> and the internal
     * <code>Polynomial</code>s are equal to each other.
     *
     * @param obj an <code>Object</code> to be tested for equality
     * @return <code>true</code> if the same function is represented,
     * <code>false</code> otherwise
     */
    @Override
    public boolean equals(final Object obj) {

    if (!(obj instanceof PolynomialFunctionRepresentation)) {
        return false;
    }
    final PolynomialFunctionRepresentation other = (PolynomialFunctionRepresentation) obj;
    if (other.poly.equals(this.poly)) {
        return true;
    }
    return false;

    }

    /**
     * Returns a hash code for this object. The hash code of the
     * interal representation (<code>Polynomial</code>) is used.
     *
     * @return an <code>int</code> representing the hash code for this
     * object
     */
    @Override
    public int hashCode() {

    if (this.poly != null) {
        return this.poly.hashCode();
    } else {
        return 0;
    }

    }


    @Override
    public boolean requiresArgument(final int position) {

        YNM value = this.requiresArgument[position];
        if (value == YNM.MAYBE) {
            value = YNM.fromBool(this.poly.containsVariable("x_"+position));
            this.requiresArgument[position] = value;
        }

    return value.toBool();

    }

    @Override
    public List<ElementPair> getDecrElementPairs(final int arity) {

    final List<ElementPair> pairs = new ArrayList<ElementPair>();
    final PolynomialElementValue defaultValue = new PolynomialElementValue(0, this.carrierSetSize);
    final Iterator<List<ElementValue>> outer = defaultValue.getElementListIterator(arity);

        while (outer.hasNext()) {
        final List<ElementValue> outerValue = outer.next();
            for (int i=0; i<arity; i++) {
                final List<ElementValue> innerValue = new ArrayList<ElementValue>(outerValue);
                final ElementValue current = innerValue.get(i);
                final ElementValue previous = current.decrement();
                if (previous != null) {
                    innerValue.set(i, previous);
                    pairs.add(new ElementPair(outerValue, innerValue));
                }
            }
    }
    return pairs;

    }


    @Override
    public Iterator<List<ElementValue>> getSmallerElements(final List<ElementValue> elementList) {
        final List<Iterable<ElementValue>> smallers = new ArrayList<Iterable<ElementValue>>(elementList.size());

        for (final ElementValue e : elementList) {
            smallers.add(new Iterable<ElementValue>() {

                @Override
                public Iterator<ElementValue> iterator() {
                    return new ElementIterator(e);
                }

            });
        }

        final boolean copies = true;
        return new ListGenerator<ElementValue>(smallers, copies);
    }


    /**
     * iterates over all elements which are smaller or equal than the initial element
     */
    private final static class ElementIterator implements Iterator<ElementValue> {

        private ElementValue current;

        public ElementIterator(final ElementValue init) {
            this.current = init;
        }

        @Override
        public boolean hasNext() {
            return this.current != null;
        }

        @Override
        public ElementValue next() {
            final ElementValue ret = this.current;
            this.current = this.current.decrement();
            return ret;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }

    };

    @Override
    public boolean isWeaklyMonotonic() {

    if (this.poly == null) {
        return true;
    }

    // VERY BAD HACK!!!! TODO: THINK OF SOMETHING BETTER!!!!

    if (this.poly.toString().indexOf("+") > -1 || this.poly.toString().indexOf("-") > -1) {
        return false;
    } else {
        return true;
    }

    }

    /**
     * Overwrites {@link java.lang.Object#toString toString} of
     * <code>Object</code> and returns a <code>String</code> of the
     * polynomial modeled by this <code>FunctionRepresentation</code>
     *
     * @return a <code>String</code> with the represented polynomial
     */
    @Override
    public String toString() {
        return this.poly.toString();
    }

    @Override
    public Iterator<FunctionRepresentation> getFunctionIterator(final int arity, final boolean needMonotonic) {

    final FunctionIterator iter = new FunctionIterator(arity);
        if (needMonotonic) {
            return new Iterator<FunctionRepresentation>() {

                FunctionRepresentation next = null;
                boolean nextValid = false;

                @Override
                public boolean hasNext() {
                    if (!this.nextValid) {
                        while (true) {
                            if (iter.hasNext()) {
                                this.next = iter.next();
                                if (this.next.isWeaklyMonotonic()) {
                                    this.nextValid = true;
                                    break;
                                }
                            } else {
                                this.next = null;
                                this.nextValid = true;
                                break;
                            }
                        }
                    }
                    return this.next != null;
                }

                @Override
                public FunctionRepresentation next() {

                    if (this.hasNext()) {
                        this.nextValid = false;
                        return this.next;
                    } else {
                        throw new NoSuchElementException();
                    }

                }

                @Override
                public void remove() {
                    throw new UnsupportedOperationException();
                }

            };
        } else {
            return iter;
        }

    }

    /*
     * Implements the Iterator over possible functions
     */
    private class FunctionIterator implements Iterator<FunctionRepresentation> {

    private final int arguments;
    private int iterCounter = 0;

    private FunctionIterator(final int arguments) {

        this.arguments = arguments;

    }

    @Override
    public boolean hasNext() {

        if (this.iterCounter <= (1 + (this.arguments * 2))) {
        return true;
        } else {
        return false;
        }

    }

    @Override
    public FunctionRepresentation next() {

        PolynomialFunctionRepresentation func = null;
        if (this.iterCounter == 0) {
        func = new PolynomialFunctionRepresentation(Polynomial.ZERO, PolynomialFunctionRepresentation.this.carrierSetSize, this.arguments);
        } else if (this.iterCounter == 1) {
        func = new PolynomialFunctionRepresentation(Polynomial.ONE, PolynomialFunctionRepresentation.this.carrierSetSize, this.arguments);
        } else if (this.iterCounter > 1 && this.iterCounter <= this.arguments + 1) {
        func = new PolynomialFunctionRepresentation(Polynomial.createVariable("x_" + (this.iterCounter - 2)), PolynomialFunctionRepresentation.this.carrierSetSize, this.arguments);
        } else if (this.iterCounter > (this.arguments + 1) && this.iterCounter <= (1 + (this.arguments * 2))) {
        final Polynomial poly = Polynomial.createVariable("x_" + (this.iterCounter - this.arguments - 2));
        func = new PolynomialFunctionRepresentation(poly.plus(Polynomial.createConstant(1)), PolynomialFunctionRepresentation.this.carrierSetSize, this.arguments);
        }
        this.iterCounter++;
        return func;

    }

    /**
     * This method is not implemented.
     *
     */
    @Override
    public void remove() {
    }

    }

    /**
     * Returns a HTML representation of this function. Implements the
     * function for the <code>HTML_Able</code> interface.
     *
     * @return an HTML <code>String</code> representing this function.
     */
    public String toHTML() {
    return this.poly.toHTML();
    }

    @Override
    public FunctionRepresentation getConstantRepresentation(final int arity) {
        return new PolynomialFunctionRepresentation(Polynomial.ZERO, this.carrierSetSize, arity);
    }

    @Override
    public String export(final Export_Util o) {
        return this.poly.toHTML();
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        return this.poly.toDOM(doc, xmlMetaData);
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return this.poly.toCPF(doc, xmlMetaData);
    }

}
