package aprove.verification.dpframework.DPProblem.Processors;

import static aprove.verification.dpframework.BasicStructures.Utility.PoloStrictMode.*;

import aprove.verification.dpframework.BasicStructures.Utility.*;

/**
 * Common superclass for QDP problem processors which use a polynomial ordering
 * and which try to orient at least one of the constraints strictly using
 * allstrict, autostrict or searchstrict as search modes.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public abstract class AbstractStrictPoloQDPProblemProcessor extends
        AbstractPoloQDPProblemProcessor {

    protected PoloStrictMode mode; // searchstrict, autostrict, allstrict
    /**
     * @param description
     */
    public AbstractStrictPoloQDPProblemProcessor(Arguments arguments) {
        super(arguments);
        this.mode = arguments.mode;
    }

    public static class Arguments extends AbstractPoloQDPProblemProcessor.Arguments {
        public PoloStrictMode mode = AUTOSTRICT;
    }

}
