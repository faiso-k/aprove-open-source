package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

/**
 * Requires an executable named "glucose" in $PATH.
 */
public class GlucoseEngine extends SatEngine {

    private static final String COMMAND = "glucose";

    @ParamsViaArgumentObject
    public GlucoseEngine(Arguments arguments) {
        super(arguments);
    }

    @Override
    public SATChecker getSATChecker() {
        return new SATRaceStdinChecker(GlucoseEngine.COMMAND);
    }

    public static class Arguments extends SatEngine.Arguments {
    }

}
