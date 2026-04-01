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
import aprove.verification.oldframework.Utility.GenericStructures.*;


public class ItpfNeg extends ItpfUnary {

    public static ItpfNeg create(Itpf child) {
        return new ItpfNeg(child, false, false);
    }

    public static ItpfNeg create(Itpf child, boolean isNormalized, boolean isDnf) {
        return new ItpfNeg(child, isNormalized, isDnf);
    }

    private ItpfNeg(Itpf child, boolean isNormalized, boolean isDnf) {
        super(child, isNormalized, isDnf);
    }

    @Override
    public boolean isNeg() {
        return true;
    }

    @Override
    public Itpf getChild() {
        return this.child;
    }

    @Override
    public ItpfNeg applySubstitutionNoCheck(TRSSubstitution sigma) {
        Itpf newChild = this.child.applySubstitution(sigma);
        if (newChild != this.child) {
            return new ItpfNeg(this.child, this.isNormalized, this.isDnf);
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
        return o.notSign() + this.child.export(o, predefinedMap, verbosityLevel);
    }

    @Override
    public int hashCode() {
        return 31 * this.child.hashCode();
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
        return this.child.equals(((ItpfNeg)obj).child);
    }

    @Override
    public Itpf visit(IItpfVisitor visitor) {
        return visitor.fcaseNeg(this) ? visitor.caseNeg(this, visitor.applyTo(this.child)) : this;
    }

    @Override
    protected Itpf doNormalization(boolean neg) {
        if (this.child.isAtom()) {
            if (neg) {
                return this.child;
            } else {
                return this;
            }
        } else {
            return this.child.normalize(!neg);
        }
    }

    @Override
    protected List<List<Itpf>> doDnf(boolean neg, LinkedList<Pair<TRSVariable, Boolean>> quantors, FreshNameGenerator boundRenaming) {
        return this.child.doDnf(!neg, quantors, boundRenaming);
    }

    @Override
    protected void collectFreeVariables(Set<TRSVariable> variables) {
        this.child.collectFreeVariables(variables);
    }
}
