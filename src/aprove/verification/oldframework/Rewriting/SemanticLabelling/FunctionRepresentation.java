package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.xml.*;

/**
 * This interface models a Function, that is used by the {@link Model
 * Model} to assign an Interpretation to a <code>FunctionSymbol</code>.
 *
 * @author <a href="mailto:chang@i2.informatik.rwth-aachen.de">Christian Hang</a>
 * @version 1.0
 */
public interface FunctionRepresentation extends Exportable,
 XMLObligationExportable, CPFAdditional {


    /**
     * Evaluates this function using the specified arguments. This
     * method is used to verify if a models holds for some rules.
     *
     * @param arguments a list of <code>ElementValue</code>s, which
     * are used as the arguments to the function call
     * @return the result of the function call for the specified
     * arguments as an <code>ElementValue</code>.
     * @throws IllegalArgumentException if <code>arguments</code> does
     * not contain the appropriate number of elements or unexpected
     * elements
     */
    public ElementValue evaluate(List<ElementValue> arguments);


    /**
     * Determines for a specified argument position, if that argument
     * is required for the function evaluation. The argument
     * positions are zero-based.
     *
     * @param position a zero-based argument position
     * @return <code>true</code> if <code>position</code> is required
     * for the function evaluation, <code>false</code> otherwise
     */
    public boolean requiresArgument(int position);

    /**
     * This method will return an <code>Iterator</code>, providing
     * <code>FunctionRepresentation</code>s for a function of the
     * specified <code>arity</code>. It is up to the implementation to
     * choose an intelligent order and subset of all possible
     * functions to facilitate the model search. The
     * <code>Iterator</code> must not return a
     * <code>FunctionRepresentation</code>, that is marked as
     * irrelevant!
     *
     * @param arity the arity of the function to be represented
     * @return an <code>Iterator</code>, providing
     * <code>FunctionRepresentation</code>s, that are not irrelevant.
     */
    public Iterator<FunctionRepresentation> getFunctionIterator(int arity, boolean needMonotonicity);


    /**
     * Determines whether this represented function is weakly
     * monotonic. It is a prerequisite for quasi-models to only
     * contain weakly monotonic functions.
     *
     * @return <code>true</code> if the represented function is weakly
     * monotonic, <code>false</code> otherwise
     */
    public boolean isWeaklyMonotonic();

    /**
     * Converts an integer into an <code>ElementValue</code>
     * representing the specified integer
     *
     * @param value an integer to be casted into an <code>ElementValue</code>
     * @return an <code>ElementValue</code> representing <code>value</code>
     */
    public ElementValue getElementValue(int value);

    /**
     * Gets a set of <code>ElementPair</code>s, consisting of all
     * pairs of elements <em>i</em>,<em>j</em> out of the carrier set
     * that fulfill the requirement <em>i &gt; j</em>.
     *
     * @return a <code>List<ElementPair></code> value
     */
    public List<ElementPair> getDecrElementPairs(int arity);

    /**
     * iterates over all lists of elements el such that
     * elementList >= el. Note that it is important that elementList itself is included.
     * This is in contrast to getDecrElementPairs where only lists el1, el2 are returned with
     * el1 > el2 !!!
     * @param elementList
     */
    public Iterator<List<ElementValue>> getSmallerElements(List<ElementValue> elementList);

    /**
     * Gets the size of the carrier set, that is used.
     *
     * @return the size of the carrier set
     */
    public int getCarrierSetSize();

    public FunctionRepresentation getConstantRepresentation(int arity);

}
