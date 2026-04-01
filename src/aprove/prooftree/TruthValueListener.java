package aprove.prooftree;

import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Logic.*;

/**
 * Interface implemented by all classes waiting for changes in the truth
 * value.
 */
public interface TruthValueListener {

    /**
     * Method invoked in the proof tree expansion whenever the truth value
     * of an obligation changed.
     *
     * @param value new truth value
     * @param source the reason for the value change (normally, another
     *  obligation which changed its truth value)
     */
    void truthValueChanged(TruthValue value, ObligationNode source);

}
