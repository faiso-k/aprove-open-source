package aprove.input.Programs.llvm.processors;

import java.util.*;

import aprove.input.Programs.llvm.problems.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.IntegerReasoning.IntegerRuleSetProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Transforms an SCC of a symbolic execution graph to a set of rules.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMSCCToRuleSetProcessor extends LLVMGraphProcessor {

    /**
     * @param arguments The parameters of this processor.
     */
    @ParamsViaArgumentObject
    public LLVMSCCToRuleSetProcessor(Arguments arguments) {
        super(arguments);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof LLVMSCCProblem;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
    throws AbortionException {
        List<Pair<String, ? extends RuleSet>> conversionLog = new LinkedList<Pair<String, ? extends RuleSet>>();
        return
            ResultFactory.proved(
                new IntegerRuleSetProblem(
                    this.translateSCCToRuleSet(((LLVMSCCProblem)obl).getSCC(), conversionLog, aborter),
                    IntegerRuleSetPurpose.TERMINATION,
                    IntegerRuleSetRewritePosition.TOPANDINNERMOST,
                    true
                ),
                YNMImplication.SOUND,
                new SCCToRuleSetProof(conversionLog)
            );
    }

    /**
     * A very fine proof.
     * @author cryingshadow
     */
    public class SCCToRuleSetProof extends LLVMGraphToRulesProof {

        /**
         * Create the proof.
         * @param l Documentation about the magic we've done in the conversion.
         */
        public SCCToRuleSetProof(List<Pair<String, ? extends RuleSet>> l) {
            super(l, "SCC2RuleSet", "LLVM SCC to Rule Set Proof");
        }

    }

}
