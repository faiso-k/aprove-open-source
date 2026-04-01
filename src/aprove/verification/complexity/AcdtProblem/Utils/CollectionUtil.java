package aprove.verification.complexity.AcdtProblem.Utils;

import java.util.*;

public class CollectionUtil {

    public static <T> Set<T> set(T... elems) {
        return new LinkedHashSet<T>(Arrays.asList(elems));
    }

}
