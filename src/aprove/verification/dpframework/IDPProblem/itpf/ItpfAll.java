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

public class ItpfAll extends ItpfQuantor {

    public static ItpfAll create(TRSVariable var, Itpf child) {
        return new ItpfAll(var, child, false, false);
    }

    protected static ItpfAll create(TRSVariable var, Itpf child, boolean isNormalized, boolean isDnf) {
        return new ItpfAll(var, child, isNormalized, isDnf);
    }

    protected final int hash;

    private ItpfAll(TRSVariable var, Itpf child, boolean isNormalized, boolean isDnf) {
        super(child, var, isNormalized, isDnf);
        this.hash = 31 * child.hashCode() + 31*31 * var.hashCode();
    }

    @Override
    public boolean isAll() {
        return true;
    }

    @Override
    public ItpfAll applySubstitutionNoCheck(TRSSubstitution sigma) {
        if (sigma.getDomain().contains(this.var)) {
            Map<TRSVariable, TRSTerm> varMap = new LinkedHashMap<TRSVariable, TRSTerm>(sigma.toMap());
            varMap.remove(this.var);
            sigma = TRSSubstitution.create(ImmutableCreator.create(varMap), true);
        }
        Itpf newChild = this.child.applySubstitution(sigma);
        if (newChild != this.child) {
            return new ItpfAll(this.var, this.child, this.isNormalized, this.isDnf);
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
        res.append(o.allQuantor());
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
        final ItpfAll other = (ItpfAll) obj;
        return this.var.equals(other.var) && this.child.equals(other.child);
    }

    @Override
    public Itpf visit(IItpfVisitor visitor) {
        return visitor.fcaseAll(this) ? visitor.caseAll(this, visitor.applyTo(this.child)) : this;
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
                return ItpfExists.create(this.var, newChild, true, false);
            }
        } else {
            Itpf newChild = this.child.normalize(false);
            if (newChild.isTrue() || newChild.isFalse()) {
                return newChild;
            } else if (newChild == this.child) {
                return this;
            } else {
                return new ItpfAll(this.var, newChild, true, false);
            }
        }
    }

}
