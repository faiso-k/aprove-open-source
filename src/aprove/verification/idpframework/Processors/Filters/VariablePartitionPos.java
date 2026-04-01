package aprove.verification.idpframework.Processors.Filters;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Algorithms.UsableRules.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author MP
 */
public class VariablePartitionPos extends IDPExportable.IDPExportableSkeleton {

    private final IVariable<?> var;
    private final IActiveAtom activeAtom;
    private final int hash;

    public VariablePartitionPos(final IVariable<?> var) {
        this(var, null);
    }

    public VariablePartitionPos(final IActiveAtom activeAtom) {
        this(null, activeAtom);
    }

    private VariablePartitionPos(final IVariable<?> var,
        final IActiveAtom activeAtom) {

        this.var = var;
        this.activeAtom = activeAtom;
        final int prime = 31;
        int result = 1;
        result = prime * result + ((activeAtom == null) ? 0 : activeAtom.hashCode());
        result = prime * result + ((var == null) ? 0 : var.hashCode());
        this.hash = result;
    }

    public IActiveAtom getActiveAtom() {
        return this.activeAtom;
    }

    public IVariable<?> getVar() {
        return this.var;
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        if (this.var != null) {
            this.var.export(sb, eu, verbosityLevel);
        } else {
            this.activeAtom.export(sb, eu, verbosityLevel);
        }

    }

    @Override
    public int hashCode() {
        return this.hash;
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
        final VariablePartitionPos other = (VariablePartitionPos) obj;
        if (this.activeAtom == null) {
            if (other.activeAtom != null) {
                return false;
            }
        } else if (!this.activeAtom.equals(other.activeAtom)) {
            return false;
        }
        if (this.var == null) {
            if (other.var != null) {
                return false;
            }
        } else if (!this.var.equals(other.var)) {
            return false;
        }
        return true;
    }

}
