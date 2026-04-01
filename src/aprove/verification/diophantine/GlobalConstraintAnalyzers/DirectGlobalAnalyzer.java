package aprove.verification.diophantine.GlobalConstraintAnalyzers;

import java.util.*;

import aprove.verification.diophantine.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Gather directly available information.
 *
 * @author fuhs
 */
public class DirectGlobalAnalyzer implements GlobalConstraintAnalyzer {

    @Override
    public DefaultValueMap<String, SearchBounds> analyze(final
            Formula<Diophantine> formula) {
        final Set<Diophantine> allGlobalConstraints = DirectGlobalAnalyzer.getAllGlobalConstraints(formula);
        final Set<SimplePolyConstraint> allGlobalSPCs = this.toSPCs(allGlobalConstraints);
        final DefaultValueMap<String, SearchBounds> res = this.gatherKnowledge(allGlobalSPCs);
        return res;
    }

    private static Set<Diophantine> getAllGlobalConstraints(final
            Formula<Diophantine> formula) {
        final GlobalAtomExtractor<Diophantine> extractor
            = new GlobalAtomExtractor<Diophantine>();
        formula.apply(extractor);
        final Set<Diophantine> res = extractor.getResult();
        return res;
    }

    private Set<SimplePolyConstraint> toSPCs(
            final Set<Diophantine> allGlobalConstraints) {
        final Set<SimplePolyConstraint> res = new LinkedHashSet<SimplePolyConstraint>();
        for (final Diophantine dio : allGlobalConstraints) {
            res.add(dio.toSimplePolyConstraint());
        }
        return res;
    }

    private DefaultValueMap<String, SearchBounds> gatherKnowledge(
            final Set<SimplePolyConstraint> spcs) {
        final DefaultValueMap<String, SearchBounds> res
            = new DefaultValueMap<String, SearchBounds>(SearchBounds.UNLIMITED);
        for (SimplePolyConstraint spc : spcs) {
            Pair<String, SearchBounds> varWithNewBound = spc.toSearchBounds();
            if (varWithNewBound != null) {
                SearchBounds oldBound = res.get(varWithNewBound.x);
                SearchBounds greatNewBound = oldBound.intersect(varWithNewBound.y);
                if (greatNewBound == null) {
                    // stability over precision! ignore contradictions on this level
                    // (no handling empty of singleton intervals this close to the deadline)
                    greatNewBound = oldBound;
                }
                res.put(varWithNewBound.x, greatNewBound);
            }
        }
        return res;
    }


}
