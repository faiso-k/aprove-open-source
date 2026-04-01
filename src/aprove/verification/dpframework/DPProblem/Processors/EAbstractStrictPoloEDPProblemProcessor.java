package aprove.verification.dpframework.DPProblem.Processors;

import static aprove.verification.dpframework.BasicStructures.Utility.PoloStrictMode.*;

import aprove.verification.dpframework.BasicStructures.Utility.*;

/**
 * Common superclass for EDP problem processors which use a polynomial ordering
 * and which try to orient at least one of the constraints strictly using
 * allstrict, autostrict or searchstrict as search modes.
 *
 * @author stein
 * @version $Id$
 */
public abstract class EAbstractStrictPoloEDPProblemProcessor extends
        EAbstractPoloEDPProblemProcessor {

    protected final PoloStrictMode mode; // searchstrict, autostrict, allstrict

    public EAbstractStrictPoloEDPProblemProcessor(Arguments arguments) {
        super(arguments);
        this.mode = arguments.mode;
    }

    public static class Arguments extends EAbstractPoloEDPProblemProcessor.Arguments {
        public PoloStrictMode mode = AUTOSTRICT;
    }

}
