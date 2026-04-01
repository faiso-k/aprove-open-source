package aprove.verification.oldframework.Utility.Profiling;


/**
 * @author Tim Enger
 */

public interface HasFeatureVector<E extends Enum<E>> {

    public FeatureVector<E> getFeatureVector();

}
