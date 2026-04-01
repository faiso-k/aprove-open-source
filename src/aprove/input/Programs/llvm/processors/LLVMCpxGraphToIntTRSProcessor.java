package aprove.input.Programs.llvm.processors;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;


public class LLVMCpxGraphToIntTRSProcessor extends LLVMSEGraphToIntTRSProcessor {

    @ParamsViaArgumentObject
    public LLVMCpxGraphToIntTRSProcessor(Arguments arguments) {
        super(arguments);
    }

    @Override
    public Result process(BasicObligation obl,
                          BasicObligationNode oblNode,
                          Abortion aborter,
                          RuntimeInformation rti) throws AbortionException {
        
        Implication implication = UpperBound.create();
        
        return process(obl, oblNode, aborter, rti, implication);
    }

}
