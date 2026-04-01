package aprove.verification.oldframework.Bytecode.Processors.ToSCC;

import aprove.prooftree.Export.Utility.*;

/**
 * Convenience parent class of all SCC analyses.
 */
public abstract class SCCAnalysis implements Exportable {
    /** {@inheritDoc} */
    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }
}
