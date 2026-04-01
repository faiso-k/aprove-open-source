package aprove.solver.Engines;

import java.util.*;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;

public class MultiSATEngine extends SatEngine {

    List<SatEngine> engines = new LinkedList<SatEngine>();

    @ParamsViaArgumentObject
    public MultiSATEngine(final Arguments arguments) {
        super(arguments);
        this.engines.add(arguments.solver1);
        if (arguments.solver2 != null) {
            this.engines.add(arguments.solver2);
        }
        if (arguments.solver3 != null) {
            this.engines.add(arguments.solver3);
        }
        if (arguments.solver4 != null) {
            this.engines.add(arguments.solver4);
        }
    }

    @Override
    public SATChecker getSATChecker() {
        final List<SATChecker> checkers = new LinkedList<SATChecker>();
        for (int i = 0; i < this.engines.size(); i++) {
            checkers.add(this.engines.get(i).getSATChecker());
        }

        return new MultiSATChecker(checkers);
    }

    public static class Arguments extends SatEngine.Arguments {
        public SatEngine solver1;
        public SatEngine solver2 = null;
        public SatEngine solver3 = null;
        public SatEngine solver4 = null;
    }

}
