package aprove.solver;

import java.util.*;

import aprove.solver.Engines.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.Processors.QDPSizeChangeProcessor.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SAT.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.OrderEncoders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

@SuppressWarnings("serial")
public class EMBFactory extends POFactory {

    protected aprove.verification.dpframework.Orders.Solvers.EMBSolver embsolver;

    @ParamsViaArgumentObject
    public EMBFactory(Arguments arguments) {
        super("EMB", arguments);
        this.embsolver = null;
    }

    @Override
    public AbortableConstraintSolver<TRSTerm> getSolver(Collection<aprove.verification.dpframework.Orders.Constraint<TRSTerm>> cons) {
        if (this.quasi) {
            Set<FunctionSymbol> sig = Constraint.getFunctionSymbols(cons);
            Set<Doubleton<FunctionSymbol>> restrictions = null;
            if (this.breadth) {
                return QEMBBreadthSolver.create(sig, restrictions);
            } else {
                return QEMBDepthSolver.create(sig, restrictions);
            }
        } else {
            if (this.embsolver == null) {
                this.embsolver = aprove.verification.dpframework.Orders.Solvers.EMBSolver.create();
            }
            return this.embsolver;
        }
    }

    public String toHTML(Map<String,Object> params) {
        StringBuffer html = new StringBuffer();
        // do something nicer below
        html.append("<UL>");

        if(!this.breadth) {
            html.append("<LI>Depth-First Search");
        }
        else {
            html.append("<LI>Breadth-First Search");
        }
        if(!this.quasi) {
            html.append("<LI>Syntactic Equivalences Only");
        }
        else {
            html.append("<LI>Allow Nonsyntactic Equivalences");
        }

    html.append("</UL>");
        // do something nicer above
        return "<B>EMB</B> (<B>"+MetaSolverFactory.getDisplayName(this.name)+"</B>)"+html.toString();
    }

    @Override
    public SATEncoder getSATEncoder(FormulaFactory<None> formulaFactory) {
        if (this.quasi) {
            return new QEMBEncoder(formulaFactory, 0, this.afsType);
        } else {
            return new EMBEncoder(formulaFactory, 0, this.afsType);
        }
    }

    @Override
    public SCNPOrderEncoder getSCNPOrderEncoder(FormulaFactory<None> formulaFactory) {
        if (this.quasi) {
            return new QEMBEncoder(formulaFactory, 0, this.afsType);
        } else {
            switch (this.afsType) {
            case NOAFS:
                return new SCNPEmbEncoder(formulaFactory);
            case MONOTONEAFS:
            case FULLAFS:
            default:
                return new EMBEncoder(formulaFactory, 0, this.afsType);
            }
        }
    }

    @Override
    public SATSCTEncoder getSATSCTEncoder(FormulaFactory<None> formulaFactory) {
        if (this.quasi) {
            return new QEMBEncoder(formulaFactory, 0, this.afsType);
        } else {
            return new EMBEncoder(formulaFactory, 0, this.afsType);
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
            this.breadth = POFactory.getDefaultBreadth("EMB");
            this.quasi = POFactory.getDefaultQuasi("EMB");
            this.restriction = POFactory.getDefaultRestriction("EMB");
        }
    }

    @Override
    public boolean deliversCPForders() {        
        return true;
    }

}
