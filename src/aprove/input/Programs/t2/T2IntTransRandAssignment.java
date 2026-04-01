package aprove.input.Programs.t2;

import java.util.Collections;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;

public class T2IntTransRandAssignment extends T2IntTransAssignment {
    /**
     * Mark that a variable gets a random value.
     * @param var some variable
     */
    public T2IntTransRandAssignment(final TRSVariable var) {
        super(var, null);
    }
    
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        this.export(new PLAIN_Util(), sb);
        return sb.toString();
    }
    
    /** {@inheritDoc} */
    @Override
    public Set<TRSVariable> getVariables() {
        return Collections.singleton(this.getVariable());
    }

    /** {@inheritDoc} */
    @Override
    public void export(final Export_Util o, final StringBuilder sb) {
        sb.append(IDPExport.exportTerm(this.getVariable(), o, IDPPredefinedMap.DEFAULT_MAP)).append(" := nondet();").append(
            o.linebreak());
    }

}
