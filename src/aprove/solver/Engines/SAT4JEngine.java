package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

public class SAT4JEngine extends SatEngine {

    private final String library;

    @ParamsViaArgumentObject
    public SAT4JEngine(final Arguments arguments) {
        super(arguments);
        this.library = arguments.library;
    }

    @Override
    public SATChecker getSATChecker() {
        return new SAT4JChecker(this.library);
    }

    public static class Arguments extends SatEngine.Arguments {
        public String library = null;
    }

}
