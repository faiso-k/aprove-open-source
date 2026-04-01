package aprove.verification.idpframework.Core.Utility.Marking;



/**
 * @author mpluecke
 */
public interface Mark<MetaDataType> {

    /**
     * When copying mark1 must be compatible with the new mark2.
     * @param mark2 New mark.
     * @return True iff mark1 is compatible with mark to.
     */
    public boolean isCompatible(final Mark<?> mark);

    public static abstract class MarkSkeleton<MetaDataType> implements Mark<MetaDataType> {
        /**
         * @param atomicMark True iff this mark is atomic.
         */
        protected MarkSkeleton() {
        }

    }
}
