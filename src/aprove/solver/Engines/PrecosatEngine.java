package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

/**
 * Requires an executable named "precosat" in $PATH.
 */
public class PrecosatEngine extends SatEngine {

    private static final String COMMAND = "precosat";

    @ParamsViaArgumentObject
    public PrecosatEngine(Arguments arguments) {
        super(arguments);
    }

    @Override
    public SATChecker getSATChecker() {
        return new SATRaceStdinChecker(PrecosatEngine.COMMAND);
    }

    public static class Arguments extends SatEngine.Arguments {
    }

}
