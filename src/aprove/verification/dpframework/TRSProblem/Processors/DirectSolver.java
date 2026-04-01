package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;

public interface DirectSolver {

    ExportableOrder<TRSTerm> solveDirect(Set<Rule> R, Abortion aborter) throws AbortionException;

}
