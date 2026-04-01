package aprove.verification.dpframework.BasicStructures;

/**
 * Objects with a pair of TRSTerms can return the TRSTerm in the lhs and in the rhs.
 */
public interface HasTermPair {

    /**
     * give the set of left hand sides of this.
     * Must return non-null value.
     */
    public TRSTerm getLeft();

    /**
     * give the set of right hand sides of this.
     * Must return non-null value.
     */
    public TRSTerm getRight();

}
