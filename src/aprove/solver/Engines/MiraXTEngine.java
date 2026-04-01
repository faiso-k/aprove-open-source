package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

public class MiraXTEngine extends SatEngine {

    private final int numThreads;
    private final boolean simp;

    @ParamsViaArgumentObject
    public MiraXTEngine(Arguments arguments) {
        super(arguments);
        this.numThreads = arguments.numThreads;
        this.simp = arguments.simp;
    }

    @Override
    public SATChecker getSATChecker() {
            return new MiraXTChecker(this.numThreads,this.simp);
    }

    public static class Arguments extends SatEngine.Arguments {
        public int numThreads = 1;
        public boolean simp = true;
    }

}
