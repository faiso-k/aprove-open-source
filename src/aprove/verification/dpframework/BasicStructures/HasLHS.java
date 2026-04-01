package aprove.verification.dpframework.BasicStructures;

/**
 * Objects with a lhs that is a TRSFunctionApplication can return this TRSFunctionApplication.
 */
public interface HasLHS {

    /**
     * give the left hand side of this.
     * Must return non-null value.
     */
    public TRSFunctionApplication getLeft();

}
