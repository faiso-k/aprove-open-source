package aprove.solver.Engines;

import java.math.*;

import aprove.solver.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class RatSolverEngine extends Engine {

    @Override
    public SearchAlgorithm getSearchAlgorithm(DefaultValueMap<String, BigInteger> ranges) {
        return RatSolverFileSearch.create(ranges);
    }
}
