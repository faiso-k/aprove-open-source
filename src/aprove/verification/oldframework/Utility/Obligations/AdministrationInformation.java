package aprove.verification.oldframework.Utility.Obligations;

import aprove.verification.dpframework.*;

/**
 * Created on 29.07.2005 by marmer
 *
 * Class which stores some information which is serialized
 * beside the root obligation node.
 *
 * @author marmer
 * @version $Id$
 */

public class AdministrationInformation {

    private ObligationAndStrategy currentTuple;

    // Public constructor for XML serialization.
    public AdministrationInformation() {

    }

    /**
     * Public getter method which should only be used by XMLEncoder.
     */
    public ObligationAndStrategy getCurrentTuple() {
        return this.currentTuple;
    }

    /**
     * Public setter method which should only be used by XMLDecoder.
     */
    public void setCurrentTuple(ObligationAndStrategy currentTuple) {
        this.currentTuple = currentTuple;
    }



}
