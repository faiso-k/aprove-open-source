package aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;

public class RecursionDepthSampleConjectureMap extends SampleConjectureMap{

    public RecursionDepthSampleConjectureMap(TRSTerm scheme, Set<AbstractRule> rules, Set<Position> rhsVariables) {
        super(scheme, rules, rhsVariables);
    }

    @Override
    BigInteger getIndex(RewriteSequence conjecture) {
        return conjecture.getRecursionDepth();
    }

    public static SampleConjectureMap fromConjecture(RewriteSequence conjecture, LowerBoundsToolbox toolbox) {
        TRSTerm t = conjecture.getResultRL();
        TRSTerm scheme = toolbox.pfHelper.abstractFromIntConstants(t);
        Set<AbstractRule> rules = conjecture.getRules();
        Set<Position> rhsVariables = new LinkedHashSet<>();
        for (Entry<TRSVariable, List<Position>> e: conjecture.getLhs().getVariablePositions().entrySet()) {
            if (conjecture.getResult().getVariables().contains(e.getKey())) {
                rhsVariables.addAll(e.getValue());
            }
        }
        return new RecursionDepthSampleConjectureMap(scheme, rules, rhsVariables);
    }

}
