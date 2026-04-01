package aprove.verification.dpframework.HaskellProblem.Processors;
/*
 * Created on 13.04.2005
 */
import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.HaskellProblem.*;

public abstract class HaskellProcessor extends Processor.ProcessorSkeleton {
    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
         return this.process((HaskellProgram)obl,oblNode,aborter);
    }

    public abstract Result process(HaskellProgram obl,Abortion aborter)  throws AbortionException ;

    public Result process(HaskellProgram obl,BasicObligationNode oblNode, Abortion aborter) throws AbortionException {
        obl.addTransformation(this);

         Result res = this.process((HaskellProgram)obl,aborter);
         if (res == null){
         res = ResultFactory.justANewStrategy(new Success(oblNode));
         }
         return res;
    }

    @Override
    public boolean isApplicable(BasicObligation obl){
        return (obl instanceof HaskellProgram)
            &&
            this.preconditionsFulfilled((HaskellProgram)obl);
    }

    /**
     * tests whether all needed preconditions are fulfilled in order to apply this processor
     * @param hp the HaskellProgram
     * @return true iff the processor is applicable
     */
    protected boolean preconditionsFulfilled(HaskellProgram hp) {
        Logger logger = Logger.getLogger("aprove.verification.dpframework.HaskellProblem.Processors.Haskell");
        List<Class<? extends HaskellProcessor>> appliedProcs = hp.getAppliedTransformations();
        Set<Class<? extends HaskellProcessor>> neededProcs = this.getPreconditionTransformations(hp);
        neededProcs.removeAll(appliedProcs);
        if (!neededProcs.isEmpty()) {
            StringBuilder sb = new StringBuilder("ERROR in Haskell Transformation ");
            sb.append(this.getClass().getSimpleName());
            sb.append(": ");
            sb.append("needed previous transformations missing: ");
            String sep = "";
            for(Class<? extends HaskellProcessor> procClass : neededProcs) {
                sb.append(sep);
                sb.append(procClass.getSimpleName());
                sep = ", ";
            }
            sb.append('\n');
            logger.log(Level.SEVERE, sb.toString());
            return false;
        }
        return true;
    }

    /**
     * gets the transformation processors that are needed in order to apply this processor
     * @param hp the current Haskell Program
     * @return the set of transformation processors needed
     */
    protected abstract Set<Class<? extends HaskellProcessor>> getPreconditionTransformations(HaskellProgram hp);

    /**
     * @return the set of all required transformation processors, i.e. these processors must be applied
     */
    protected Set<Class<? extends HaskellProcessor>> getAllRequiredTransformationProcessors() {
        Set<Class<? extends HaskellProcessor>> procs = new LinkedHashSet<Class<? extends HaskellProcessor>>();
        procs.add(BindingReductionProcessor.class);
        procs.add(CaseReductionProcessor.class);
        procs.add(CondReductionProcessor.class);
        procs.add(IfReductionProcessor.class);
        procs.add(IrrPatReductionProcessor.class);
        procs.add(LambdaReductionProcessor.class);
        procs.add(LetReductionProcessor.class);
        procs.add(NewTypeReductionProcessor.class);
        procs.add(NumReductionProcessor.class);
        return procs;
    }

}
