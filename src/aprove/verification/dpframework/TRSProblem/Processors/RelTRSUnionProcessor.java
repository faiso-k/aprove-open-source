package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Transform the relative termination problem R/S into the full termination
 * problem R \cup S. This is sound, but very incomplete.
 *
 * @author ulrichsg
 */
@NoParams
public class RelTRSUnionProcessor extends RelTRSProcessor {

    @Override
    protected Result processRelTRS(RelTRSProblem problem, Abortion aborter,
            RuntimeInformation rti) throws AbortionException {

        Set<Rule> allRules = new LinkedHashSet<Rule>(problem.getR().size() + problem.getS().size());
        for (Rule rRule : problem.getR()) {
            allRules.add(rRule);
        }
        for (Rule sRule : problem.getS()) {
            allRules.add(sRule);
        }
        QTRSProblem result = QTRSProblem.create(ImmutableCreator.create(allRules));
        return ResultFactory.proved(result, YNMImplication.SOUND, RelTRSUnionProof.create());
    }

    public static class RelTRSUnionProof extends RelTRSProof {

        private static final RelTRSUnionProof instance = new RelTRSUnionProof();

        public static RelTRSUnionProof create() {
            return RelTRSUnionProof.instance;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Built union of R and S.";
        }

    }
}
