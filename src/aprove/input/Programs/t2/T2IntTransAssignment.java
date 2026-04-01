package aprove.input.Programs.t2;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import immutables.*;

public class T2IntTransAssignment implements Immutable, T2IntTransBodyStatement {
    private final TRSVariable variable;
    private final TRSTerm value;

    public T2IntTransAssignment(final TRSVariable var, final TRSTerm val) {
        this.variable = var;
        this.value = val;
    }

    public TRSVariable getVariable() {
        return this.variable;
    }

    public TRSTerm getValue() {
        return this.value;
    }

    /** {@inheritDoc} */
    @Override
    public Set<TRSVariable> getVariables() {
        final Set<TRSVariable> res = this.value.getVariables();
        res.add(this.variable);
        return res;
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
        sb.append(IDPExport.exportTerm(this.variable, o, IDPPredefinedMap.DEFAULT_MAP)).append(" := ").append(
            IDPExport.exportTerm(this.value, o, IDPPredefinedMap.DEFAULT_MAP)).append(";").append(o.linebreak());
    }
}
