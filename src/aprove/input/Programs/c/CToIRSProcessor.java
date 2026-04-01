package aprove.input.Programs.c;

import java.io.*;

import aprove.input.Programs.intProg.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Parses a C program as an IRSProblem if the C program adheres to the restricted grammar for C Integer Programs.
 * @author cryingshadow
 * @version $Id$
 */
public class CToIRSProcessor extends Processor.ProcessorSkeleton {

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.Processor#isApplicable(aprove.prooftree.Obligations.BasicObligation)
     */
    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof CProblem && ((CProblem)obl).getQuery().isMain();
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.Processor#process(aprove.prooftree.Obligations.BasicObligation, aprove.prooftree.Obligations.BasicObligationNode, aprove.strategies.Abortions.Abortion, aprove.strategies.ExecutableStrategies.RuntimeInformation)
     */
    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
    throws AbortionException {
        CProblem cObl = (CProblem)obl;
        Translator intProgTranslator = new Translator();
        try {
            intProgTranslator.translate(new File(cObl.getPath()));
        } catch (FileNotFoundException | TranslationException e) {
            return ResultFactory.unsuccessful(e.getMessage());
        }
        return
            ResultFactory.proved(
                (IRSProblem)intProgTranslator.getState(),
                YNMImplication.EQUIVALENT,
                new CToIRSProof()
            );
    }

    /**
     * A proof that we parsed a C file as IRSProblem.
     * @author cryingshadow
     * @version $Id$
     */
    public static class CToIRSProof extends DefaultProof {

        /**
         * Default constructor.
         */
        public CToIRSProof() {
            // empty
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Utility.VerbosityExportable#export(aprove.prooftree.Export.Utility.Export_Util, aprove.verification.oldframework.Utility.VerbosityLevel)
         */
        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Parsed C Integer Program as IRS.";
        }

    }

}
