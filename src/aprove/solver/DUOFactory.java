package aprove.solver;

import java.util.logging.*;

import aprove.solver.Engines.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.OrderEncoders.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * @author Carsten Fuhs
 */
public class DUOFactory extends SolverFactory {

    private static final Logger log = Logger.getLogger("aprove.solver.DUOFactory");

    // factory for the orders encapsulated by this order
    private final SolverFactory order1;
    private final SolverFactory order2;

    @ParamsViaArgumentObject
    public DUOFactory(Arguments arguments) {
        super(arguments);
        this.order1 = arguments.order1;
        this.order2 = arguments.order2;
    }

    @Override
    public QActiveSolver getQActiveSolver() {
        SatEngine satEngine = this.checkEngine(this.getEngine());
        if (DUOFactory.log.isLoggable(Level.INFO)) {
            DUOFactory.log.info("ENGINE: " + satEngine + "\n");
        }

        return new QDPDUOSolver(this, this.order1, this.order2, satEngine);
    }

    @Override
    public SCNPOrderEncoder getSCNPOrderEncoder(FormulaFactory<None> formulaFactory) {
        return new SCNPDUOEncoder(formulaFactory, this.order1, this.order2);
    }

    private SatEngine checkEngine(Engine engine) {
        if (!(engine instanceof SatEngine)) {
            engine = new SAT4JEngine(new SAT4JEngine.Arguments());
        }
        return (SatEngine) engine;
    }

    public static class Arguments extends SolverFactory.Arguments {

        public SolverFactory order1;
        public SolverFactory order2;

    }

    @Override
    public boolean deliversCPForders() {        
        return this.order1.deliversCPForders() && this.order2.deliversCPForders();
    }

}
