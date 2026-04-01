package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

/**
 * Requires an executable named "clasp" in $PATH.
 * Version 1.3.4 should do.
 */
public class ClaspEngine extends SatEngine {

    private static final String COMMAND = "clasp";
    private String heuristic;

    @ParamsViaArgumentObject
    public ClaspEngine(Arguments arguments) {
        super(arguments);
        this.heuristic = arguments.heuristic;
    }

    @Override
    public SATChecker getSATChecker() {
        String args = "--heuristic=" + this.heuristic;
        return new SATRaceStdinChecker(ClaspEngine.COMMAND, args);
    }

    public static class Arguments extends SatEngine.Arguments {
        public String heuristic = "Berkmin";
    }
}
