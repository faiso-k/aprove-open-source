package aprove.verification.dpframework.HaskellProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.oldframework.Haskell.Transformations.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * @author Stephan Swiderski
 */
@NoParams
public class NumReductionProcessor extends HaskellProcessor {
    protected static Logger logger = Logger.getLogger("aprove.verification.theoremprover.Haskell");


    @Override
    protected Set<Class<? extends HaskellProcessor>> getPreconditionTransformations(HaskellProgram hp) {
        Set<Class<? extends HaskellProcessor>> procs = new LinkedHashSet<Class<? extends HaskellProcessor>>();
        procs.add(LetReductionProcessor.class);
        return procs;
    }


    @Override
    public Result process(HaskellProgram obj, Abortion aborter) {
        HaskellProgram hp = (HaskellProgram) obj;
        hp = (HaskellProgram) hp.deepcopy();
        if (NumReduction.applyTo(hp.getModules(),aborter)) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("Num Reduction does");
            }

            Proof proof = new NumReductionProof(obj, hp);

            // This processor is only SOUND, not COMPLETE
            // This is because the representation of Int is unbounded,
            // and therefore a program like f (x+1) = f (x+2::Int) would  be found non-terminating,
            // while bounded Ints make it terminate at x=maxBound::Int-1
            //
            // Char has the same problem
            //
            // For Floats, we can represent any precision, while Haskell is (usually) bound to some IEE754 type,
            // which means that a program such as f x = if (x+0.1 == x) then True else f (x*x) would terminate
            // for IEE754, while we could find it to be non-terminating

            return ResultFactory.proved(hp,YNMImplication.SOUND, proof);
        } else {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("Num Reduction fail");
            }

            return null;
        }
    }

}
