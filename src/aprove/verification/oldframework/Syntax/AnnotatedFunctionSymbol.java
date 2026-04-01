package aprove.verification.oldframework.Syntax;

/**
 * An <code>interface</code> to access annotated
 * <code>FunctionSymbol</code>s which can hold additional
 * information.
 *
 * @author <a href="mailto:chang@ariadne.informatik.rwth-aachen.de">Christian Hang</a>
 * @version $Id$
 */
public interface AnnotatedFunctionSymbol {

    /**
     * Accessor method to retrieve the object annotating this symbol.
     *
     * @return the annotation of this symbol
     */
    public Object getObject();

    /**
     * Sets the annotation of this symbol to a new <code>Object</code>
     *
     * @param newAnnotation the new annotation of this symbol
     */
    public void setObject(Object newAnnotation);

    /**
     * Convenience method to get access to the symbol's name without
     * casting it to an actual FunctionSymbol
     *
     * @return the name of the symbol
     */
    public String getName();

}
