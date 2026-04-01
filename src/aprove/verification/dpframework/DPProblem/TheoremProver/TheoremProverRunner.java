package aprove.verification.dpframework.DPProblem.TheoremProver;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public interface TheoremProverRunner {

    public Pair<Boolean, Exportable> runTheoremProverOnInput(Formula frml,
                                                             Program prgrm,
                                                             String strategy,
                                                             String timeLimit,
                                                             Abortion aborter,
                                                             RuntimeInformation rti) throws AbortionException,
                                                                                     TheoremProverFailedException;
}
