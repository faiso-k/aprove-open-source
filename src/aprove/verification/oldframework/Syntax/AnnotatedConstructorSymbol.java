package aprove.verification.oldframework.Syntax;

import java.util.*;

import aprove.verification.oldframework.Utility.Graph.*;

/**
 * A <code>ConstructorSymbol</code> which can hold additional
 * information. It has an <code>Object</code> associated with it.
 *
 * @author <a href="mailto:chang@ariadne.informatik.rwth-aachen.de">Christian Hang</a>
 * @version $Id$
 */
public class AnnotatedConstructorSymbol extends ConstructorSymbol implements AnnotatedFunctionSymbol, PrettyStringable {

    /**
     * The <code>Object</code> containing the annotation of the symbol
     */
    private Object annotation;

    /**
     * Creates a new <code>AnnotatedConstructorSymbol</code> instance,
     * without initial annotation.
     *
     * @param name name of the new symbol
     * @param argsorts the <code>Sort</code>s of the arguments
     * @param sort the <code>Sort</code> of the symbol
     * @see ConstructorSymbol
     */
    public AnnotatedConstructorSymbol(String name, List<Sort> argsorts, Sort sort) {

    super(name, argsorts, sort);

    }

    /**
     * Creates a new <code>AnnotatedConstructorSymbol</code> instance,
     * with an initial annotation.
     *
     * @param name name of the new symbol
     * @param argsorts the <code>Sort</code>s of the arguments
     * @param sort the <code>Sort</code> of the symbol
     * @param annotation an <code>Object</code> annotating the symbol
     * @see ConstructorSymbol
     */
    public AnnotatedConstructorSymbol(String name, List<Sort> argsorts, Sort sort, Object annotation) {

    super(name, argsorts, sort);
    this.annotation = annotation;

    }

    /**
     * Accessor method to retrieve the object annotating this symbol.
     *
     * @return the annotation of this symbol
     */
    @Override
    public Object getObject() {

    return this.annotation;

    }

    /**
     * Sets the annotation of this symbol to a new <code>Object</code>
     *
     * @param newAnnotation the new annotation of this symbol
     */
    @Override
    public void setObject(Object newAnnotation) {

    this.annotation = newAnnotation;

    }

    @Override
    public int hashCode() {

    return super.hashCode();

    }

    @Override
    public String prettyToString() {

    return this.getName() + "(" + this.getObject().toString() + ")";

    }

    @Override
    public boolean equals(Object obj) {

    if (obj instanceof SyntacticFunctionSymbol) {
        SyntacticFunctionSymbol symbol = (SyntacticFunctionSymbol) obj;
        if (symbol instanceof AnnotatedConstructorSymbol) {
        return (symbol.getName().equals(this.getName()) && ((AnnotatedConstructorSymbol) obj).annotation.equals(this.annotation));
        } else {
        return symbol.getName().equals(this.getName());
        }
    }
    return false;

    }

}
