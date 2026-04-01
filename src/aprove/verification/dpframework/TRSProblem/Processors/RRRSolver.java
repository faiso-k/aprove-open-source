package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;

/**
 * Interface for all RRR solvers
 * @see DirectSolver
 * @author Andreas Kelle-Emden
 */
public interface RRRSolver {

        boolean isRRRApplicable(Set<Rule> R);

        ExportableOrder<TRSTerm> solveRRR(Set<Rule> R, Abortion aborter) throws AbortionException;

}
