package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

public class MiniSAT09ZEngine extends SatEngine {

    private boolean simp;

    @ParamsViaArgumentObject
    public MiniSAT09ZEngine(Arguments arguments) {
        super(arguments);
        this.simp = arguments.simp;
    }

    @Override
    public SATChecker getSATChecker() {
            return new MiniSAT09ZChecker(this.simp);
    }

    public static class Arguments extends SatEngine.Arguments {
        public boolean simp = false;
    }

}
