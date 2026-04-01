package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

/**
 * Requires an executable named "cryptominisat" in $PATH.
 */
public class CryptoMiniSATEngine extends SatEngine {

    private static final String COMMAND = "cryptominisat";

    private int verbosity;

    @ParamsViaArgumentObject
    public CryptoMiniSATEngine(Arguments arguments) {
        super(arguments);
        if (arguments.verbosity >= 2) {
            this.verbosity = 2;
        }
        else if (arguments.verbosity <= 0) {
            this.verbosity = 0;
        }
        else {
            this.verbosity = arguments.verbosity;
        }
    }

    @Override
    public SATChecker getSATChecker() {
        return new SATRaceStdinChecker(CryptoMiniSATEngine.COMMAND, "--verbosity="+this.verbosity);
    }

    public static class Arguments extends SatEngine.Arguments {
        public int verbosity = 0;
    }
}
