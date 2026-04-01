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

@SuppressWarnings("serial")
public class RPOSFactory extends POFactory {

    @ParamsViaArgumentObject
    public RPOSFactory(Arguments arguments) {
        super("RPOS", arguments);
    }


    @Override
    public AbortableConstraintSolver<TRSTerm> getSolver(Collection<aprove.verification.dpframework.Orders.Constraint<TRSTerm>> cons) {
        Set<FunctionSymbol> sig = Constraint.getFunctionSymbols(cons);
        if (this.quasi) {
            Set<Doubleton<FunctionSymbol>> restrictions = null;
            if (this.breadth) {
                return QRPOSBreadthSolver.create(sig, restrictions);
            } else {
                return QRPOSDepthSolver.create(sig, restrictions);
            }
        } else {
            if (this.breadth) {
                return RPOSBreadthSolver.create(sig);
            } else {
                return RPOSDepthSolver.create(sig);
            }
        }
    }

    @Override
    public SATEncoder getSATEncoder(FormulaFactory<None> formulaFactory) {
        if (this.quasi) {
            return new QRPOSEncoder(formulaFactory, 0, this.afsType);
        } else {
            return new RPOSEncoder(formulaFactory, 0, this.afsType);
        }
    }

    @Override
    public SCNPOrderEncoder getSCNPOrderEncoder(FormulaFactory<None> formulaFactory) {
        if (this.quasi) {
            return new QRPOSEncoder(formulaFactory, 0, this.afsType);
        } else {
            return new RPOSEncoder(formulaFactory, 0, this.afsType);
        }
    }

    @Override
    public SATSCTEncoder getSATSCTEncoder(FormulaFactory<None> formulaFactory) {
        if (this.quasi) {
            return new QRPOSEncoder(formulaFactory, 0, this.afsType);
        } else {
            return new RPOSEncoder(formulaFactory, 0, this.afsType);
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
            this.breadth = POFactory.getDefaultBreadth("RPOS");
            this.quasi = POFactory.getDefaultQuasi("RPOS");
            this.restriction = POFactory.getDefaultRestriction("RPOS");
        }
    }
    
    @Override
    public boolean deliversCPForders() {
        return true;
    }


}
