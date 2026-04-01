package aprove.verification.oldframework.Utility.GenericStructures;

/**
 * Converts objects of one type to objects of another type.
 * @author cryingshadow
 * @version $Id$
 * @param <I> The input type.
 * @param <O> The output type.
 */
public interface Converter<I, O> {

    /**
     * @param input The input object.
     * @return The output object.
     */
    O convert(I input);

}
