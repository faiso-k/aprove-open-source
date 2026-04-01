package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

public class PICOSATEngine extends SatEngine {

    private static final String COMMAND = "picosat";

    @ParamsViaArgumentObject
    public PICOSATEngine(Arguments arguments) {
        super(arguments);
    }

    @Override
    public SATChecker getSATChecker() {
        return new SATRaceStdinChecker(PICOSATEngine.COMMAND);
    }
}
