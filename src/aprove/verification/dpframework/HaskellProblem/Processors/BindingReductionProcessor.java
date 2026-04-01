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
public class BindingReductionProcessor extends HaskellProcessor {
    protected static Logger logger = Logger.getLogger("aprove.verification.dpframework.HaskellProblem.Processors.Haskell");

    @Override
    protected Set<Class<? extends HaskellProcessor>> getPreconditionTransformations(HaskellProgram hp) {
        Set<Class<? extends HaskellProcessor>> procs = new LinkedHashSet<Class<? extends HaskellProcessor>>();
        procs.add(IrrPatReductionProcessor.class);
        return procs;
    }

    @Override
    public Result process(HaskellProgram obj, Abortion aborter) {
        HaskellProgram hp = obj;
        hp = (HaskellProgram) hp.deepcopy();
        BindingReductionProof proof = new BindingReductionProof(obj, hp);
        if (BindingReduction.applyTo(hp.getModules(),proof,aborter)) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("Binding Reduction does");
            }

            return ResultFactory.proved(hp,YNMImplication.EQUIVALENT, proof);
        } else {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("Binding Reduction fail");
            }

            return null;
        }
    }

}
