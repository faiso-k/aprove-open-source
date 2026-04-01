package aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.BasicStructures.*;

public class IdentitySampleConjectureMap extends SampleConjectureMap {

    public IdentitySampleConjectureMap(TRSTerm scheme, Set<AbstractRule> rules, Set<Position> rhsVariables) {
        super(scheme, rules, rhsVariables);
    }

    @Override
    BigInteger getIndex(RewriteSequence conjecture) {
        TRSTerm natTerm = null;
        for (TRSTerm t: conjecture.getLhs().getSubTerms()) {
            if (PFHelper.isInt(t)) {
                if (natTerm == null) {
                    natTerm = t;
                } else {
                    return null;
                }
            }
        }
        if (natTerm == null) {
            return null;
        } else {
            return PFHelper.toInt(natTerm);
        }
    }

    public static SampleConjectureMap fromConjecture(RewriteSequence conjecture, LowerBoundsToolbox toolbox) {
        TRSTerm t = conjecture.getResultRL();
        TRSTerm scheme = toolbox.pfHelper.abstractFromIntConstants(t);
        if (scheme.getVariables().size() > 1) {
            return null;
        }
        Set<AbstractRule> rules = conjecture.getRules();
        Set<Position> rhsVariables = new LinkedHashSet<>();
        for (Entry<TRSVariable, List<Position>> e: conjecture.getLhs().getVariablePositions().entrySet()) {
            if (conjecture.getResult().getVariables().contains(e.getKey())) {
                rhsVariables.addAll(e.getValue());
            }
        }
        return new IdentitySampleConjectureMap(scheme, rules, rhsVariables);
    }

}
