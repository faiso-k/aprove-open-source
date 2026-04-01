package aprove.input.Programs.t2;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import immutables.*;

public class T2IntTransGuard implements Immutable, T2IntTransBodyStatement {
    private final TRSTerm guard;

    public T2IntTransGuard(final TRSTerm g) {
        this.guard = g;
    }

    public TRSTerm getGuard() {
        return this.guard;
    }

    /** {@inheritDoc} */
    @Override
    public Set<TRSVariable> getVariables() {
        return this.guard.getVariables();
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        this.export(new PLAIN_Util(), sb);
        return sb.toString();
    }
    
    /** {@inheritDoc} */
    @Override
    public void export(final Export_Util o, final StringBuilder sb) {
        sb.append("assume(").append(IDPExport.exportTerm(this.guard, o, IDPPredefinedMap.DEFAULT_MAP)).append(");").append(
            o.linebreak());
    }
}
