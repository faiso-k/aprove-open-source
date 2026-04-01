package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

public class MINISAT2IncrementalEngine extends SatEngine {

    private final boolean simp;

    @ParamsViaArgumentObject
    public MINISAT2IncrementalEngine(Arguments arguments) {
        super(arguments);
        this.simp = arguments.simp;
    }

    @Override
    public SATChecker getSATChecker() {
        return new MiniSAT2IncrementalFileChecker(this.simp);
    }

    public static class Arguments  extends SatEngine.Arguments{
        public boolean simp = true;
    }
}
