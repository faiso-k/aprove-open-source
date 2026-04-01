package aprove.verification.dpframework.PiDPProblem.Processors;

import static aprove.verification.dpframework.BasicStructures.Utility.PoloStrictMode.*;

import aprove.verification.dpframework.BasicStructures.Utility.*;

/**
 * Common superclass for PiDP problem processors which use a polynomial ordering
 * and which try to orient at least one of the constraints strictly using
 * allstrict, autostrict or searchstrict as search modes.
 *
 * @author Carsten Fuhs
 */
public abstract class AbstractStrictPoloPiDPProblemProcessor extends
        AbstractPoloPiDPProblemProcessor {

    protected final PoloStrictMode mode; // searchstrict, autostrict, allstrict

    public AbstractStrictPoloPiDPProblemProcessor(Arguments arguments) {
        super(arguments);
        this.mode = arguments.mode;
    }

    public static class Arguments extends AbstractPoloPiDPProblemProcessor.Arguments {
        public PoloStrictMode mode = AUTOSTRICT;
    }

}
