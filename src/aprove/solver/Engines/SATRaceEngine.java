package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

/**
 * Allows to use an arbitrary SAT Race / SAT Competition compliant
 * SAT solver as by the I/O format description on
 *
 * http://www.satcompetition.org/2009/format-solvers2009.html
 *
 * The call is
 *
 *   command + " " + args + " " + filename
 */
public class SATRaceEngine extends SatEngine {

    private String command;
    private String args;

    @ParamsViaArgumentObject
    public SATRaceEngine(Arguments arguments) {
        super(arguments);
        this.command = arguments.command;
        this.args = arguments.args;
    }

    @Override
    public SATChecker getSATChecker() {
        return new SATRaceFileChecker(this.command, this.args);
    }

    public static class Arguments extends SatEngine.Arguments {
        public String command;
        public String args = "";
    }
}
