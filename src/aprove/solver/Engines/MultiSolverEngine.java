package aprove.solver.Engines;

import java.math.*;

import aprove.solver.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class MultiSolverEngine extends Engine {
    private MultiSolverFileSearch.Backend backend = MultiSolverFileSearch.Backend.VALENCIA;

    @Override
    public SearchAlgorithm getSearchAlgorithm(DefaultValueMap<String, BigInteger> ranges) {
        return MultiSolverFileSearch.create(ranges, this.backend);
    }

    public void setBackend(MultiSolverFileSearch.Backend backend) {
        this.backend = backend;
    }
}
