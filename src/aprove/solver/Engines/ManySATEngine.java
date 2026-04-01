package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

/**
 * Requires an executable named "manysat11" in $PATH.
 */
public class ManySATEngine extends SatEngine {

    private static final String COMMAND = "manysat11";

    @ParamsViaArgumentObject
    public ManySATEngine(Arguments arguments) {
        super(arguments);
    }

    @Override
    public SATChecker getSATChecker() {
        return new SATRaceStdinChecker(ManySATEngine.COMMAND);
    }

    public static class Arguments extends SatEngine.Arguments {
    }
}
