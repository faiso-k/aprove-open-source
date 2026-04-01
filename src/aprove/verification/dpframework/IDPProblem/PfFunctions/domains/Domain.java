package aprove.verification.dpframework.IDPProblem.PfFunctions.domains;

import aprove.prooftree.Export.Utility.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public abstract class Domain implements Immutable, Exportable {

    /**
     * The domain suffix
     */
    protected final String suffix;

    Domain(String suffix) {
        this.suffix = suffix;
    }

    public String getSuffix() {
        return this.suffix;
    }

    public boolean isIntegerDomain() {
        return false;
    }

    public boolean isBooleanDomain() {
        return false;
    }

    @Override
    public final String toString() {
        return this.export(new PLAIN_Util());
    }

}
