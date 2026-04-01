package aprove.input.Programs.llvm.processors;

import java.util.*;

import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IntegerReasoning.processors.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * This processor takes a symbolic execution graph SCC and translates it to an ITRS problem by converting each edge of
 * the SCC to an ITRS rewrite rule and simplifying these.
 */
public class LLVMSCCToITRS extends LLVMGraphProcessor {

    /**
     * @param arguments The parameters of this processor.
     */
    @ParamsViaArgumentObject
    public LLVMSCCToITRS(Arguments arguments) {
        super(arguments);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof LLVMSCCProblem);
    }
    
    /**
     * Work on the given obligation.
     * @param obl a TerminationGraphProblem
     * @param oblNode ignored.
     * @param aborter some aborter
     * @param rti ignored.
     * @return one obligation per SCC
     */
    @Override
    public Result process(
        BasicObligation obl,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti
    ) {
        SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> scc = ((LLVMSCCProblem)obl).getSCC();
        List<Pair<String, ? extends RuleSet>> conversionLog = new LinkedList<>();
        //Get rules:
        Set<IGeneralizedRule> iGRules =
            this.simplifyRuleSet(
                this.translateSCCToRuleSet(scc, conversionLog, aborter),
                conversionLog,
                aborter,
                /*allowOverapproximation=*/true,
                /*filterFreeVarsFromCond=*/false,
                null
            );
        return
            ResultFactory.proved(
                IntegerRuleSetToITRSProcessor.transformToITRS(iGRules),
                YNMImplication.SOUND,
                new SCCToITRSProof(conversionLog)
            );
    }

    /**
     * A very fine proof.
     * @author Marc Brockschmidt
     */
    public class SCCToITRSProof extends LLVMGraphToRulesProof {

        /**
         * Create the proof.
         * @param l Documentation about the magic we've done in the conversion.
         */
        public SCCToITRSProof(List<Pair<String, ? extends RuleSet>> l) {
            super(l, "SCC2ITRS", "LLVM SCC to ITRS Proof");
        }

    }

}
