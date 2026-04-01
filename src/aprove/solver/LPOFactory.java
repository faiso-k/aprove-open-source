package aprove.solver;

import java.util.*;

import aprove.solver.Engines.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.Processors.QDPSizeChangeProcessor.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SAT.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

public class LPOFactory extends POFactory {

    @ParamsViaArgumentObject
    public LPOFactory(Arguments arguments) {
        super("LPO", arguments);
    }


    @Override
    public AbortableConstraintSolver<TRSTerm> getSolver(Collection<aprove.verification.dpframework.Orders.Constraint<TRSTerm>> cons) {
        Set<FunctionSymbol> sig = Constraint.getFunctionSymbols(cons);
        if (this.quasi) {
            Set<Doubleton<FunctionSymbol>> restrictions = null;
            if (this.breadth) {
                return QLPOBreadthSolver.create(sig, restrictions);
            } else {
                return QLPODepthSolver.create(sig, restrictions);
            }
        } else {
            if (this.breadth) {
                return LPOBreadthSolver.create(sig);
            } else {
                return LPODepthSolver.create(sig);
            }
        }
    }

    @Override
    public SATEncoder getSATEncoder(FormulaFactory<None> formulaFactory) {
        if (this.quasi) {
            return new NewQLPOEncoder(formulaFactory, 0, this.afsType);
        } else {
            return new NewLPOEncoder(formulaFactory, 0, this.afsType);
        }
    }

    @Override
    public SCNPOrderEncoder getSCNPOrderEncoder(FormulaFactory<None> formulaFactory) {
        if (this.quasi) {
            return new NewQLPOEncoder(formulaFactory, 0, this.afsType);
        } else {
            return new NewLPOEncoder(formulaFactory, 0, this.afsType);
        }
    }

    @Override
    public SATSCTEncoder getSATSCTEncoder(FormulaFactory<None> formulaFactory) {
        if (this.quasi) {
            return new NewQLPOEncoder(formulaFactory, 0, this.afsType);
        } else {
            return new NewLPOEncoder(formulaFactory, 0, this.afsType);
        }
    }

    @Override
    protected Engine checkEngine(Engine engine) {
        if (engine instanceof SatEngine) {
            return engine;
        }
        if (engine instanceof YNMPEVLEngine) {
            return engine;
        }
        return new YNMPEVLEngine();
    }

    public static class Arguments extends POFactory.Arguments {
        {
            this.breadth = POFactory.getDefaultBreadth("LPO");
            this.quasi = POFactory.getDefaultQuasi("LPO");
            this.restriction = POFactory.getDefaultRestriction("LPO");
        }
    }

    @Override
    public boolean deliversCPForders() {
        return true;
    }
}
