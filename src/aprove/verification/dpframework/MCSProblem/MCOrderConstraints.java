package aprove.verification.dpframework.MCSProblem;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Set of order constraints between variables for use in MC transition rules.
 * @author fuhs
 */
public class MCOrderConstraints implements HasVariables, Exportable, Immutable {

    // /map/ a variable pair to an orientation from GE, GT, EQ, LE, LT
    private final ImmutableMap<MCVarPair, MCRelation> constraints;

    private MCOrderConstraints(ImmutableMap<MCVarPair, MCRelation> varsToRelation) {
        this.constraints = varsToRelation;
    }

    public static MCOrderConstraints createFromMCVarPairMap(ImmutableMap<MCVarPair, MCRelation> varsToRelation) {
        return new MCOrderConstraints(varsToRelation);
    }

    /**
     * @param varsToRelation - non-null, must not contain trivially
     *  inconsistent information like "x > y" and "y > x"
     * @return
     */
    public static MCOrderConstraints createFromVarPairMap(Map<Pair<TRSVariable, TRSVariable>, MCRelation> varsToRelation) {
        Map<MCVarPair, MCRelation> protoConstraints = new LinkedHashMap<MCVarPair, MCRelation>();
        for (Entry<Pair<TRSVariable, TRSVariable>, MCRelation> varsToRel : varsToRelation.entrySet()) {
            Pair<TRSVariable, TRSVariable> key = varsToRel.getKey();
            TRSVariable v1 = key.x;
            TRSVariable v2 = key.y;
            Pair<MCVarPair, MCRelation> varPairToRel = MCVarPair.toEntry(v1, v2, varsToRel.getValue());
            MCRelation presentRel = protoConstraints.put(varPairToRel.x, varPairToRel.y);
            assert presentRel == null : "Trivially inconsistent information in " + varsToRelation;
        }
        return new MCOrderConstraints(ImmutableCreator.create(protoConstraints));
    }

    @Override
    public Set<TRSVariable> getVariables() {
        Set<TRSVariable> result = new LinkedHashSet<TRSVariable>();
        for (Entry<MCVarPair, MCRelation> varToRel : this.constraints.entrySet()) {
            MCVarPair varPair = varToRel.getKey();
            result.add(varPair.getFirst());
            result.add(varPair.getSecond());
        }
        return result;
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder res = new StringBuilder();
        boolean first = true;
        for (Entry<MCVarPair, MCRelation> varPairRel : this.constraints.entrySet()) {
            if (first) {
                first = false;
            }
            else {
                res.append(',');
            }
            MCVarPair varPair = varPairRel.getKey();
            res.append(varPair.getFirst().export(o));
            res.append(varPairRel.getValue().export(o));
            res.append(varPair.getSecond().export(o));
        }
        return res.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public TRSTerm toITRSConjunction(IDPPredefinedMap predefMap) {
        if (this.constraints.size() == 0) {
            return predefMap.getBooleanTrue().getTerm();
        }
        TRSTerm result = null; // unset at the beginning
        FunctionSymbol and = predefMap.getSym(Func.Land, DomainFactory.BOOLEAN);
        for (Entry<MCVarPair, MCRelation> varPairToRel : this.constraints.entrySet()) {

            // make a term out of x rel y ...
            MCVarPair varPair = varPairToRel.getKey();
            MCRelation rel = varPairToRel.getValue();
            FunctionSymbol relSym = rel.toFunctionSymbol(predefMap);
            ArrayList<TRSTerm> vars = new ArrayList<TRSTerm>(2);
            vars.add(varPair.getFirst());
            vars.add(varPair.getSecond());
            TRSTerm entryAsTerm = TRSTerm.createFunctionApplication(relSym, vars);
            vars = null;

            // ... and "conjunct" it to result
            if (result == null) {
                result = entryAsTerm;
            } else {
                ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(2);
                args.add(result);
                args.add(entryAsTerm);
                result = TRSTerm.createFunctionApplication(and, args);
                args = null;
            }
        }
        return result;
    }


    /**
     * @return the constraints
     */
    public ImmutableMap<MCVarPair, MCRelation> getConstraints() {
        return this.constraints;
    }
}
