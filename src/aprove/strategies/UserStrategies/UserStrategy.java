package aprove.strategies.UserStrategies;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.ExecutableStrategies.*;
import immutables.*;


/**
 * a user strategy is one that a user can type in.
 * Their semantics is defined via executable strategies
 * in aprove/doc/processors/processors2.
 *
 * A user strategy can be exported to be displayed. Moreover
 * it is immutable.
 * @author thiemann
 *
 */

public abstract class UserStrategy implements Exportable, Immutable {

    @Override
    public abstract String export(Export_Util o);

    @Override
    public final String toString() {
        return this.export(new PLAIN_Util());
    }

    /**
     * returns the corresponding executableStrategy if it is executed at position pos with
     * the given runtime information rti
     */
    public abstract ExecutableStrategy getExecutableStrategy(BasicObligationNode pos, RuntimeInformation rti);

    /**
     * Returns <code>true</code> if the strategy is applicable to the obligation.
     * This default implementation here returns always <code>true</code>.
     * @param obl the obligation in question
     * @return <code>true</code>
     */
    public boolean isApplicable(BasicObligation obl) {
        return true;
    }

}
