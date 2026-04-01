package aprove.verification.oldframework.Utility.Profiling;

import java.util.*;

import aprove.*;

/**
 * @author Tim Enger
 */

public class FeatureVector<E extends Enum<E>> {
    private final String type;
    private final EnumMap<E, Integer> features;

    public FeatureVector(String type, EnumMap<E, Integer> features) {
        this.type = type;
        this.features = features;
        // make sure that the feature vector is complete
        if (Globals.useAssertions) {
            Object[] allFeatures =
                features.entrySet().iterator().next().getKey().getClass().getEnumConstants();
            StringBuilder missingFeatures = new StringBuilder();
            for (int i = 0; i < allFeatures.length; i++) {
                if (!features.containsKey(allFeatures[i])) {
                    missingFeatures.append(allFeatures[i].toString() + ',');
                }
            }
            assert missingFeatures.length() == 0 : "Missing features in vector: " + missingFeatures.toString();
        }
    }

    public String getType() {
        return this.type;
    }

    public Iterable<Integer> getFeatures() {
        return this.features.values();
    }
}
