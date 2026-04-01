package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

public class SATDumpEngine extends SatEngine {

    private SatEngine engine;
    private String path;

    @ParamsViaArgumentObject
    public SATDumpEngine(Arguments arguments) {
        super(arguments);
        this.engine = arguments.engine;
        this.path = arguments.path;

    }

    @Override
    public SATChecker getSATChecker() {

        return new SATDumper(this.engine, this.path);
    }

    public static class Arguments extends SatEngine.Arguments {
        public SatEngine engine = new MINISATEngine(new MINISATEngine.Arguments());
        public String path = "/tmp/";
    }

}
