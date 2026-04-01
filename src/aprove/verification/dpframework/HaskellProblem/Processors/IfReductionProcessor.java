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
public class IfReductionProcessor extends HaskellProcessor {
    protected static Logger logger = Logger.getLogger("aprove.verification.theoremprover.Haskell");


    @Override
    protected Set<Class<? extends HaskellProcessor>> getPreconditionTransformations(HaskellProgram hp) {
        return new LinkedHashSet<Class<? extends HaskellProcessor>>();
    }


    @Override
    public Result process(HaskellProgram obj, Abortion aborter) {
        HaskellProgram hp = (HaskellProgram) obj;
        hp = (HaskellProgram) hp.deepcopy();
        IfReductionProof proof = new IfReductionProof(obj, hp);
        if (IfReduction.applyTo(hp.getModules(),proof,aborter)) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("If Reduction does");
            }

            return ResultFactory.proved(hp,YNMImplication.EQUIVALENT, proof);
        } else {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("If Reduction fail");
            }

            return null;
        }
    }

}
