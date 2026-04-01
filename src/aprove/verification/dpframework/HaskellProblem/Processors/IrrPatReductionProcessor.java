package aprove.verification.dpframework.HaskellProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.oldframework.Haskell.Transformations.*;
import aprove.verification.oldframework.Logic.*;

/**
 * @author Stephan Swiderski
 */
@NoParams
public class IrrPatReductionProcessor extends HaskellProcessor {
    protected static Logger logger = Logger.getLogger("aprove.verification.theoremprover.Haskell");

    @Override
    protected Set<Class<? extends HaskellProcessor>> getPreconditionTransformations(HaskellProgram hp) {
        Set<Class<? extends HaskellProcessor>> procs = new LinkedHashSet<Class<? extends HaskellProcessor>>();

        List<Class<? extends HaskellProcessor>> appliedProcsAfter;
        appliedProcsAfter = hp.getAppliedTransformationsAfter(IrrPatReductionProcessor.class);
        if (appliedProcsAfter != null) {
            procs.add(NewTypeReductionProcessor.class);
        }

        return procs;
    }


    @Override
    public Result process(HaskellProgram obj, Abortion aborter) {
        HaskellProgram hp = (HaskellProgram) obj;
        hp = (HaskellProgram) hp.deepcopy();
        IrrPatReductionProof proof = new IrrPatReductionProof(obj, hp);
        if (IrrPatReduction.applyTo(hp.getModules(),proof,aborter)) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("IrrPat Reduction does");
            }

            return ResultFactory.proved(hp,YNMImplication.EQUIVALENT, proof);
        } else {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("IrrPat Reduction fail");
            }

            return null;
        }
    }

}
