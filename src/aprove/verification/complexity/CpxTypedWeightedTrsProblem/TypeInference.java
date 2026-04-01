package aprove.verification.complexity.CpxTypedWeightedTrsProblem;

import java.util.LinkedHashSet;
import java.util.Set;

import aprove.verification.complexity.CpxWeightedTrsProblem.*;
import aprove.verification.complexity.LowerBounds.Types.*;


/**
 * Type Inference for CpxWeightedTrs, using Complexity.Lowerbounds.
 *
 * @author mnaaf
 *
 */
public class TypeInference {

    public static CpxTypedWeightedTrsProblem inferTypes(CpxWeightedTrsProblem trs) {
        //convert rules to lower bound class
        Set<aprove.verification.complexity.LowerBounds.BasicStructures.Rule> lowerRules = new LinkedHashSet<>();
        for (WeightedRule r : trs.getRules()) {
            lowerRules.add(new aprove.verification.complexity.LowerBounds.BasicStructures.Rule(r.getLeft(), r.getRight()));
        }
        TrsTypes types = aprove.verification.complexity.LowerBounds.Types.TypeInference.infer(lowerRules, trs.getSignature(), trs.getDefinedSymbols());
        CpxTypedWeightedTrsProblem res = CpxTypedWeightedTrsProblem.create(trs.getRules(), trs.getSignature(), types, trs.isInnermost());
        assert res.getDefinedSymbols().equals(trs.getDefinedSymbols());
        return res;
    }

}
