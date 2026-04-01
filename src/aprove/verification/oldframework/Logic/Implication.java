package aprove.verification.oldframework.Logic;

import aprove.prooftree.Export.Utility.*;

/**
 * Abstract interface for implications
 * @author Christian Kaeunicke
 * @version $Id$
 */

public interface Implication extends Exportable {

    @SuppressWarnings("serial")
    public class IncompatibleTruthValueException extends Exception{
        public IncompatibleTruthValueException(String string) {
            super(string);
        }
    }

    public TruthValue propagate(TruthValue other) throws IncompatibleTruthValueException;
}
