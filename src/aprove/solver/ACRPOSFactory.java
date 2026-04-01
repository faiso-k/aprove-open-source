package aprove.solver;

import java.util.*;

import aprove.solver.Engines.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

@SuppressWarnings("serial")
public class ACRPOSFactory extends POFactory {

    @ParamsViaArgumentObject
    public ACRPOSFactory(Arguments arguments) {
        super("ACRPOS",  arguments);
    }

    @Override
    public AbortableConstraintSolver<TRSTerm> getACSolver(Collection<Constraint<TRSTerm>> cons, Set<FunctionSymbol> rSig,
            Set<FunctionSymbol> asig, Set<FunctionSymbol> acsig, Set<FunctionSymbol> csig) {

        List<String> sigS = new LinkedList<String>();
        for(FunctionSymbol f:rSig) {
            sigS.add(f.toString()+"_"+f.getArity());
        }
        List<String> asigS = new LinkedList<String>();
        for(FunctionSymbol f:asig) {
            asigS.add(f.toString()+"_"+f.getArity());
        }
        List<String> acsigS = new LinkedList<String>();
        for(FunctionSymbol f:acsig) {
            acsigS.add(f.toString()+"_"+f.getArity());
        }
        List<String> csigS = new LinkedList<String>();
        for(FunctionSymbol f:csig) {
            csigS.add(f.toString()+"_"+f.getArity());
        }


        if (this.quasi) {
            Set<Doubleton<String>> restrictions = null;
            return ACQRPOSBreadthSolver.create(sigS, asigS, acsigS, csigS, restrictions);
        } else {
            return ACRPOSBreadthSolver.create(new ArrayList<FunctionSymbol>(rSig), new ArrayList<FunctionSymbol>(asig),
                    new ArrayList<FunctionSymbol>(acsig), new ArrayList<FunctionSymbol>(csig));
        }
    }

    /**
     * Returns true iff factory is AC compatible
     */
    @Override
    public boolean isACCompatible() {
        return true;
    }

    @Override
    protected Engine checkEngine(Engine engine) {
        if (engine instanceof YNMPEVLEngine) {
            return engine;
        }
        return new YNMPEVLEngine();
    }

    public static class Arguments extends POFactory.Arguments {
        {
            this.breadth = POFactory.getDefaultBreadth("ACRPOS");
            this.quasi = POFactory.getDefaultQuasi("ACRPOS");
            this.restriction = POFactory.getDefaultRestriction("ACRPOS");
        }
    }

    @Override
    public boolean deliversCPForders() {        
        return false;
    }
}
