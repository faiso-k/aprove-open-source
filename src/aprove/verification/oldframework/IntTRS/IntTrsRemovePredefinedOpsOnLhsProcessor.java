package aprove.verification.oldframework.IntTRS;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

public class IntTrsRemovePredefinedOpsOnLhsProcessor extends Processor.ProcessorSkeleton {

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        IRSLike irs = (IRSLike) obl;
        Set<IGeneralizedRule> rules = irs.getRules();
        Set<IGeneralizedRule> newRules = TerminationSCCToIDPv1Processor.removePredefinedOpsOnLhs(rules, IDPPredefinedMap.DEFAULT_MAP);
        if (!rules.equals(newRules)) {
            return ResultFactory.proved(irs.create(newRules, irs.getStartTerm()), YNMImplication.EQUIVALENT, new IntTRSRemovedPredefinedOpsOnLhsProof());
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof IRSLike;
    }

    public class IntTRSRemovedPredefinedOpsOnLhsProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("returned predefined operators from lhss");
        }

    }
}
