package aprove.verification.idpframework.Processors.Poly;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class RelationNode<R extends SemiRing<R>> extends IDPExportable.IDPExportableSkeleton implements HasSignum, Immutable {

    public final IVariable<R> var;

    public RelationNode(final IVariable<R> var) {
        this.var = var;
    }

    public IVariable<R> getVariable() {
        return this.var;
    }

    @Override
    public Signum getSignum() {
        return this.var != null ? this.var.getSignum() : null;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.var == null) ? 0 : this.var.hashCode());
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final RelationNode<?> other = (RelationNode<?>) obj;
        if (this.var == null) {
            if (other.var != null) {
                return false;
            }
        } else if (!this.var.equals(other.var)) {
            return false;
        }
        return true;
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        if (this.var != null) {
            this.var.export(sb, eu, verbosityLevel);
        } else {
            sb.append("1");
        }

    }

}
