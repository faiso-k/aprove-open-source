package aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem;

import java.util.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;


public class IndefiniteGroupingCriterion implements GroupingCriterion {

    @Override
    public boolean fits(SampleConjectureMap map, RewriteSequence conjecture) {
        Set<AbstractRule> rules = conjecture.getRules();
        return map.rulesEqual(rules);
    }

}
