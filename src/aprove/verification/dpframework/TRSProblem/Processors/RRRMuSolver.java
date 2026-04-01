package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Interface for RRR solvers with mu-monotonicity for CSR problems
 * @see RRRSolver
 * @author Andreas Kelle-Emden
 */
public interface RRRMuSolver {

    public boolean isRRRMuApplicable(Set<Rule> R, ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu);

    public ExportableOrder<TRSTerm> solveRRRMu(Set<Rule> R, ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu, Abortion aborter) throws AbortionException;

}
