/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class ItpfUra extends ItpfAtom {

    public static ItpfUra create(IUsableRulesEstimation eu, RelDependency k, TRSTerm t, ItpRelation rel) {
        return new ItpfUra(eu, k,  t, rel);
    }

    private final IUsableRulesEstimation eu;
    private final RelDependency k;
    private final TRSTerm t;
    private final ItpRelation rel;
    private final int hash;

    private ItpfUra(IUsableRulesEstimation eu, RelDependency k, TRSTerm t, ItpRelation rel) {
        super();
        this.eu = eu;
        this.k = k;
        this.t = t;
        this.rel = rel;
        final int prime = 31;
        int result = 1;
        result = prime * result + ((eu == null) ? 0 : eu.hashCode());
        result = prime * result + k.hashCode();
        result = prime * result + rel.hashCode();
        result = prime * result + t.hashCode();
        this.hash = result;
    }

    @Override
    public boolean isUra() {
        return true;
    }

    @Override
    public Itpf applySubstitutionNoCheck(TRSSubstitution sigma) {
        return this;
    }

    @Override
    public int hashCode() {
        return this.hash;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final ItpfUra other = (ItpfUra) obj;
        return this.k == other.k && this.rel == other.rel && this.t.equals(other.t) && (this.eu == other.eu || (this.eu != null && this.eu.equals(other.eu)));
    }

    @Override
    protected final List<List<Itpf>> doDnf(boolean neg, LinkedList<Pair<TRSVariable, Boolean>> quantors, FreshNameGenerator boundRenaming) {
        ArrayList<Itpf> inner = new ArrayList<Itpf>(1);
        List<List<Itpf>> outer = new ArrayList<List<Itpf>>(1);
        outer.add(inner);
        if (neg) {
            inner.add(ItpfNeg.create(this, true, true));
        } else {
            inner.add(this);
        }
        return outer;
    }

    @Override
    public Itpf visit(IItpfVisitor visitor) {
        return visitor.fcaseUra(this) ? visitor.caseUra(this) : this;
    }

    @Override
    protected void collectFreeVariables(Set<TRSVariable> variables) {
        // variables.addAll(t.getVariables());
    }

    @Override
    protected final Itpf doNormalization(boolean neg) {
        if (neg) {
            return ItpfNeg.create(this, true, true);
        } else {
            return this;
        }
    }

    @Override
    protected void collectFunctionSymbols(Set<FunctionSymbol> fs) {
        this.t.collectFunctionSymbols(fs);
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String export(Export_Util o) {
        return this.export(o, null, VerbosityLevel.MIDDLE);
    }

    @Override
    public String export(Export_Util o, IDPPredefinedMap predefinedMap, VerbosityLevel verbosityLevel) {
        StringBuilder sb = new StringBuilder();
        sb.append("(U");
        sb.append(o.sup(this.k.getK().toString()));
        sb.append(", ");
        sb.append(IDPExport.exportTerm(this.t, o, predefinedMap));
        sb.append(", ");
        sb.append(this.rel.export(o));
        sb.append(")");
        return sb.toString();
    }

}
