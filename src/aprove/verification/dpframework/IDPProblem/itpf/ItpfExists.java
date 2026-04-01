/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class ItpfExists extends ItpfQuantor {

    public static ItpfExists create(TRSVariable var, Itpf child) {
        return new ItpfExists(var, child, false, false);
    }

    protected static ItpfExists create(TRSVariable var, Itpf child, boolean isNormalized, boolean isDnf) {
        return new ItpfExists(var, child, isNormalized, isDnf);
    }

    protected final int hash;

    private ItpfExists(TRSVariable var, Itpf child, boolean isNormalized, boolean isDnf) {
        super(child, var, isNormalized, isDnf);
        this.hash = 19 * child.hashCode() + 31*31 * var.hashCode();
    }

    @Override
    public boolean isExists() {
        return true;
    }

    @Override
    public ItpfExists applySubstitutionNoCheck(TRSSubstitution sigma) {
        if (sigma.getDomain().contains(this.var)) {
            Map<TRSVariable, TRSTerm> varMap = new LinkedHashMap<TRSVariable, TRSTerm>(sigma.toMap());
            varMap.remove(this.var);
            sigma = TRSSubstitution.create(ImmutableCreator.create(varMap), true);
        }
        Itpf newChild = this.child.applySubstitution(sigma);
        if (newChild != this.child) {
            return new ItpfExists(this.var, this.child, this.isNormalized, this.isDnf);
        } else {
            return this;
        }
    }

    @Override
    public String export(Export_Util o) {
        return this.export(o, null, VerbosityLevel.MIDDLE);
    }

    @Override
    public String export(Export_Util o, IDPPredefinedMap predefinedMap, VerbosityLevel verbosityLevel) {
        StringBuilder res = new StringBuilder();
        res.append(o.existQuantor());
        res.append(" ");
        res.append(IDPExport.exportTerm(this.var, o, predefinedMap));
        res.append(": ");
        res.append(this.child.export(o, predefinedMap, verbosityLevel));
        return res.toString();
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
        final ItpfExists other = (ItpfExists) obj;
        return this.var.equals(other.var) && this.child.equals(other.child);
    }

    @Override
    public Itpf visit(IItpfVisitor visitor) {
        return visitor.fcaseExists(this) ? visitor.caseExists(this, visitor.applyTo(this.child)) : this;
    }

    @Override
    protected Itpf doNormalization(boolean neg) {
        if (!this.child.getFreeVariables().contains(this.var)) {
            return this.child.normalize(neg);
        }
        if (neg) {
            Itpf newChild = this.child.normalize(true);
            if (newChild.isTrue() || newChild.isFalse()) {
                return newChild;
            } else {
                return ItpfAll.create(this.var, newChild, true, false);
            }
        } else {
            Itpf newChild = this.child.normalize(false);
            if (newChild.isTrue() || newChild.isFalse()) {
                return newChild;
            } else if (newChild == this.child) {
                return this;
            } else {
                return new ItpfExists(this.var, newChild, true, false);
            }
        }
    }

}
