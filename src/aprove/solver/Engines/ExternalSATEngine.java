package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

/**
 * Generic SAT engine class for the external SAT checker class.
 * You may specify the command and the argument pattern in the strategy.
 * But you may prefer to create a subclass with given command and pattern.
 *
 * @author Andreas Kelle-Emden
 */
public class ExternalSATEngine extends SatEngine {

    private String command;
    private String argumentPattern;

    @ParamsViaArgumentObject
    public ExternalSATEngine(Arguments arguments) {
        super(arguments);
        this.command         = arguments.command;
        this.argumentPattern = arguments.argumentPattern;
    }

    @Override
    public SATChecker getSATChecker() {
            return new ExternalSATChecker(this.command, this.argumentPattern);
    }

    public static class Arguments extends SatEngine.Arguments {
        public String command;
        public String argumentPattern;
    }

}
