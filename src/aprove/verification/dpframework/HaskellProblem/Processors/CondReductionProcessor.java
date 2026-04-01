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
public class CondReductionProcessor extends HaskellProcessor {
    protected static Logger logger = Logger.getLogger("aprove.verification.theoremprover.Haskell");


    @Override
    protected Set<Class<? extends HaskellProcessor>> getPreconditionTransformations(HaskellProgram hp) {
        Set<Class<? extends HaskellProcessor>> procs = new LinkedHashSet<Class<? extends HaskellProcessor>>();
        procs.add(BindingReductionProcessor.class);
        return procs;
    }


    @Override
    public Result process(HaskellProgram obj, Abortion aborter) {
        HaskellProgram hp = (HaskellProgram) obj;
        Map copyMap = new HashMap();
        Copy.copyMap = copyMap;
        hp = (HaskellProgram) hp.deepcopy();
        Copy.copyMap = null;
        CondReductionProof proof = new CondReductionProof(obj, hp);
        if (CondReduction.applyTo(hp.getModules(),proof,copyMap,aborter)) {

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("Cond Reduction does");
            }

        return ResultFactory.proved(hp,YNMImplication.EQUIVALENT, proof);
    } else {
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("Cond Reduction fail");
        }

        return null;
    }
    }

}
