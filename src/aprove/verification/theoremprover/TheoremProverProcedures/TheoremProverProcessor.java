/*
 * Created on 31.08.2004
 *
 */
package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.LemmaDatabase.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Visitors.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;


/**
 * Class is the base class for theorem prover's processors
 * @author rabe
 * @version $Id$
 */
public abstract class TheoremProverProcessor extends Processor.ProcessorSkeleton {

    private static final boolean reallyCheckLemmaDatabase = false;

    private boolean checkLemmaDatabase;

    public TheoremProverProcessor() {
        this(true);
    }

    public TheoremProverProcessor(boolean checkLemmaDatabase) {
        this.checkLemmaDatabase = checkLemmaDatabase;
    }

    /**
     * A TheoremProverProcessor is only applicable on a TheoremProverObligation.
     * By default the processors are not applicable when we try to do an indirect proof.
     *
     * @see Processor
     */
    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof TheoremProverObligation) {
            TheoremProverObligation theorem_obl = (TheoremProverObligation) obl;
            return !theorem_obl.isIndirectProof();
        }
        return false;
    }

    /**
     * Method started by strategy framework
     */

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {

        int currentDepth = oblNode.getDepth();

        if( currentDepth > TheoremProverObligation.getMaxDepth()) {
            return ResultFactory.notApplicable();
        }

        // chech if processor is applicable
        if(obl instanceof TheoremProverObligation ) {

            TheoremProverObligation theoremProverObligation =
                (TheoremProverObligation)obl;

            if( this.checkLemmaDatabase && TheoremProverProcessor.reallyCheckLemmaDatabase) {
                // check if a instance of the obligation is contained in the lemma database,
                // if so don't start start processor

                Set<Formula> generalisations = new LinkedHashSet<Formula>();
                LemmaDatabase ldb = LemmaDatabaseFactory.getLemmmaDatabase();

                if(ldb.getSize() > 0){
                    // do it only when there lemmas
                    // otherwise it gets unnecessary slow for large formulas

                    generalisations = ldb.retrieveGeneralisations(
                            GetAllPermutationsVisitor.apply(theoremProverObligation.getFormula()));

                    if( !generalisations.isEmpty() ) {
                        return ResultFactory.proved(new LemmaDatabaseProof(generalisations.iterator().next()));
                    }
                }
            }

            return this.process(theoremProverObligation, oblNode, aborter, rti);
        }

        return ResultFactory.notApplicable();
    }

    /**
     * Method should be over written by theorem prover processor.
     * @param obligationInput Input obligation
     * @return Result of processor
     * @throws AbortionException
     */
    protected abstract Result process(TheoremProverObligation obligationInput, BasicObligationNode obligationNode, Abortion aborter,
            RuntimeInformation rti ) throws AbortionException;

}
