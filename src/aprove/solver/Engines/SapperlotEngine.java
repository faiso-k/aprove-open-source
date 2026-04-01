package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

public class SapperlotEngine extends SatEngine {

    @ParamsViaArgumentObject
    public SapperlotEngine(Arguments arguments) {
        super(arguments);
    }

    @Override
    public SATChecker getSATChecker() {
            return new SapperlotChecker();
    }

    public static class Arguments extends SatEngine.Arguments {
    }

}
