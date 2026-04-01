package aprove.solver.Engines;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

public class YicesSATEngine extends SatEngine {

    @ParamsViaArgumentObject
    public YicesSATEngine(Arguments arguments) {
        super(arguments);
    }

    @Override
    public SATChecker getSATChecker() {
        return new YicesFileChecker();
    }

}
