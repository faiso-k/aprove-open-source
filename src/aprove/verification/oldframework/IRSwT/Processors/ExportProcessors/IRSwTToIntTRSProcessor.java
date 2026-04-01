package aprove.verification.oldframework.IRSwT.Processors.ExportProcessors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Bytecode.Processors.PathLength.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IRSwT.*;
import aprove.verification.oldframework.IRSwT.IRSwTFormatTransformer.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Turns an IRSwT into an IDP in a quite simple way:
 * If R' is the given integer rewrite system, then we set
 * P = R', R = E, Q = E [here E = the empty set!] to define the IDP (Q,P,R).
 * @author Matthias Hoelzel
 */
public class IRSwTToIntTRSProcessor extends Processor.ProcessorSkeleton {
    /** Constructor! */
    public IRSwTToIntTRSProcessor() {
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return (obl instanceof IRSwTProblem && !((IRSwTProblem) obl).isBounded());
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        final IRSwTProblem intTRS = (IRSwTProblem) obl;

        final IDPPredefinedMap predefinedMap = IDPPredefinedMap.DEFAULT_MAP;
        Set<IGeneralizedRule> iGRules = PathLength.translateIGRuleSet(intTRS.getRules(), predefinedMap);

        Map<IGeneralizedRule,IGeneralizedRule> map = new HashMap<>();

        iGRules = IRSwTFormatTransformer.transformRules(iGRules, RoundingBehaviour.UNKNOWN, predefinedMap, map);
        iGRules = TerminationSCCToIDPv1Processor.cleanConstraints(iGRules, false, true, predefinedMap, aborter);
        iGRules = TerminationSCCToIDPv1Processor.removeTrivialConstraints(iGRules, predefinedMap);
        iGRules = TerminationSCCToIDPv1Processor.removePredefinedOpsOnLhs(iGRules, predefinedMap);
        iGRules = IRSwTFormatTransformer.makeLhsLinear(iGRules, predefinedMap);

        return ResultFactory.proved(
            new IRSwTProblem(ImmutableCreator.create(iGRules)),
            YNMImplication.SOUND,
            new IRSwTToIntTRSProof());
    }

    /**
     * A truly gross proof!
     * @author Matthias Hoelzel
     */
    public class IRSwTToIntTRSProof extends DefaultProof {
        /** Constructor! */
        public IRSwTToIntTRSProof() {
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Applied path-length measure to transform intTRS with terms to intTRS.";
        }
    }
}
