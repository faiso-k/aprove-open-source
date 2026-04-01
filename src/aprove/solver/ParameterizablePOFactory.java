package aprove.solver;

import aprove.solver.Engines.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.Orders.SAT.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * A factory for freely parameterizable path orderings.
 * @author Ulrich Schmidt-Goertz
 */
@SuppressWarnings("serial")
public class ParameterizablePOFactory extends POFactory {

    private final boolean multiset;
    private final boolean lex;
    private final boolean permute;
    private final boolean prec;
    private final boolean xgengrc;

    @ParamsViaArgumentObject
    public ParameterizablePOFactory(Arguments arguments) {
        super("PPO", arguments);
        this.multiset = arguments.multiset;
        this.lex = arguments.lex;
        this.permute = arguments.permute;
        this.prec = arguments.prec;
        this.xgengrc = arguments.xgengrc;
    }

    @Override
    public SATEncoder getSATEncoder(FormulaFactory<None> formulaFactory) {

        return new ParameterizablePOEncoder(formulaFactory, this.quasi,
                this.multiset, this.lex, this.permute, this.prec,
                this.xgengrc, 0, this.afsType);
    }

    @Override
    public SCNPOrderEncoder getSCNPOrderEncoder(FormulaFactory<None> formulaFactory) {

        return new ParameterizablePOEncoder(formulaFactory, this.quasi,
                this.multiset, this.lex, this.permute, this.prec,
                this.xgengrc, 0, this.afsType);
    }

    @Override
    protected Engine checkEngine(Engine engine) {
        if (engine instanceof SatEngine) {
            return engine;
        }
        return new SAT4JEngine(new SAT4JEngine.Arguments());
    }

    public static class Arguments extends POFactory.Arguments {
        public boolean multiset;
        public boolean lex;
        public boolean permute;
        public boolean prec;
        public boolean xgengrc;

        {
            this.breadth = POFactory.getDefaultBreadth("PPO");
            this.quasi = POFactory.getDefaultQuasi("PPO");
            this.restriction = POFactory.getDefaultRestriction("PPO");
        }
    }
    
    @Override
    public boolean deliversCPForders() {
        return true;
    }

}
