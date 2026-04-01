package aprove.verification.diophantine.GlobalConstraintAnalyzers;

import aprove.verification.diophantine.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Utterly ignores its input, but is rather fast at doing so.
 *
 * @author fuhs
 */
public class TrivialGlobalAnalyzer implements GlobalConstraintAnalyzer {

    @Override
    public DefaultValueMap<String, SearchBounds> analyze(
            Formula<Diophantine> formula) {
        return new DefaultValueMap<String, SearchBounds>(SearchBounds.UNLIMITED);
    }
}
