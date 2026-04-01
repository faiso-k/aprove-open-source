package aprove.verification.dpframework.BasicStructures;

/**
 * Objects with a rhs that is a term can return this term.
 */
public interface HasRHS {

	/**
     * give right hand side of this. Must return non-null value.
     */
    public TRSTerm getRight();

}
