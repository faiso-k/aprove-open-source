package aprove.verification.diophantine;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Extract information from a Formula&lt;Diophantine&gt; about the ranges
 * that one need not exceed for analyzing satisfiability of the formula.
 * @author fuhs
 */
public interface GlobalConstraintAnalyzer {

    /**
     * @param formula
     * @return deduced knowledge about the ranges to consider for
     *  <code>formula</code> -- must not impose harsher constraints
     *  than <code>formula</code>
     */
    public DefaultValueMap<String, SearchBounds> analyze(Formula<Diophantine> formula);
}
