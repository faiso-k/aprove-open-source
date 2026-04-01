package aprove.verification.dpframework.PATRSProblem;

import java.util.*;

import aprove.verification.dpframework.Utility.*;
import immutables.*;

public class PATRSPredefinedNames {

    public final static ImmutableSet<String> PREDEFINED;
    static {
        Set<String> remove_symbols = new HashSet<String>();
        remove_symbols.add("+");
        remove_symbols.add("-");
        remove_symbols.add("0");
        remove_symbols.add("1");
        PREDEFINED = ImmutableCreator.create(remove_symbols);
    }

    public static CollectionNameProvider getNameProvider() {
        return CollectionNameProvider.create(PATRSPredefinedNames.PREDEFINED);
    }
}
