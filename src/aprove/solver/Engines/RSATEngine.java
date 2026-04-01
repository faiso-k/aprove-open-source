package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

public class RSATEngine extends SatEngine {

    @ParamsViaArgumentObject
    public RSATEngine(Arguments arguments) {
        super(arguments);
    }

    @Override
    public SATChecker getSATChecker() {
        return new RSATFileChecker();
    }

}
