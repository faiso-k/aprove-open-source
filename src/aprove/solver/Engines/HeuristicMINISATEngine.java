package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

public class HeuristicMINISATEngine extends SatEngine {

    private final int limit;

    @ParamsViaArgumentObject
    public HeuristicMINISATEngine(Arguments arguments) {
        super(arguments);
        this.limit = arguments.limit;
    }

    public static class Arguments extends SatEngine.Arguments {
        public int limit = 100;
    }

    @Override
    public SATChecker getSATChecker() {
        return new HeuristicMiniSATChecker(this.limit);
    }

}
