package aprove.verification.oldframework.WeightedIntTrs;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


/**
 * The result of a WeightedArgumentFilterProcessor. It is a pair of another inner pair and a collection map from
 * function symbols to integers. The inner pair has a set of generalized integer rules as its first and a map from
 * function symbols to function symbols as its second component.
 * TODO document the meaning of the components
 * @author Jera Hensel
 * @version $Id$
 */
public class WeightedArgumentFilterResult<T extends AbstractWeightedIntRule<T>>
extends Pair<Pair<Set<T>, Map<FunctionSymbol, FunctionSymbol>>, CollectionMap<FunctionSymbol, Integer>> {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = -6909426833822644822L;

    /**
     * A constructor is a constructor is a constructor...
     * @param key A pair of a set of generalized integer rules and a map from function symbols to function symbols.
     * @param value A collection map from function symbols to integers.
     */
    public WeightedArgumentFilterResult(
        Pair<Set<T>, Map<FunctionSymbol, FunctionSymbol>> key,
        CollectionMap<FunctionSymbol, Integer> value
    ) {
        super(key, value);
    }

}
