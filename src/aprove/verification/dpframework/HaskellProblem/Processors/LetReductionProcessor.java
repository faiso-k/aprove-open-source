package aprove.verification.dpframework.HaskellProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.oldframework.Haskell.Transformations.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 */
@NoParams
public class LetReductionProcessor extends HaskellProcessor {
    protected static Logger logger = Logger.getLogger("aprove.verification.theoremprover.Haskell");


    @Override
    protected Set<Class<? extends HaskellProcessor>> getPreconditionTransformations(HaskellProgram hp) {
        Set<Class<? extends HaskellProcessor>> procs = new LinkedHashSet<Class<? extends HaskellProcessor>>();

        procs.add(NewTypeReductionProcessor.class);
        procs.add(IrrPatReductionProcessor.class);

        return procs;
    }


    @Override
    protected boolean preconditionsFulfilled(HaskellProgram hp) {
        List<Class<? extends HaskellProcessor>> appliedProcsAfter;
        appliedProcsAfter = hp.getAppliedTransformationsAfter(NewTypeReductionProcessor.class);
        Set<Class<? extends HaskellProcessor>> neededProcs = this.getPreconditionTransformations(hp);
        if (appliedProcsAfter != null) {
            neededProcs.remove(NewTypeReductionProcessor.class);
            neededProcs.removeAll(appliedProcsAfter);
        }
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
            LetReductionProcessor.logger.log(Level.SEVERE, sb.toString());
            return false;
        }

        return appliedProcsAfter.contains(IrrPatReductionProcessor.class)
            && (!appliedProcsAfter.contains(LetReductionProcessor.class));
    }


    @Override
    public Result process(HaskellProgram obj, Abortion aborter) {
        HaskellProgram hp = (HaskellProgram) obj;
        Map copyMap = new HashMap();
        Copy.copyMap = copyMap;
        hp = (HaskellProgram) hp.deepcopy();
        Copy.copyMap = null;
        LetReductionProof proof = new LetReductionProof(obj, hp);
        if (LetReduction.applyTo(hp.getModules(),proof,copyMap,aborter)) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("Let Reduction does");
            }

            return ResultFactory.proved(hp,YNMImplication.EQUIVALENT, proof);
        } else {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("Let Reduction fail");
            }

            //return ResultFactory.unsuccessful();
            return null;
        }
    }

}
