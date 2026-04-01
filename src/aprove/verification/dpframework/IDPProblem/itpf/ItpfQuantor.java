/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public abstract class ItpfQuantor extends ItpfUnary {

    protected final TRSVariable var;

    protected ItpfQuantor(Itpf child, TRSVariable var, boolean isNormalized, boolean isDnf) {
        super(child, isNormalized, isDnf);
        this.var = var;
    }

    public TRSVariable getVar() {
        return this.var;
    }

    @Override
    public final boolean isQuantor() {
        return true;
    }

    @Override
    protected List<List<Itpf>> doDnf(boolean neg, LinkedList<Pair<TRSVariable, Boolean>> quantors, FreshNameGenerator boundRenaming) {
        List<List<Itpf>> childDnf = this.child.doDnf(neg, quantors, boundRenaming);
        String newVarName = boundRenaming.getFreshName(this.var.getName(), false);
        TRSVariable newVar;
        if (newVarName.equals(this.var.getName())) {
            newVar = this.var;
        } else {
            newVar = TRSTerm.createVariable(newVarName);
            TRSSubstitution sigma = TRSSubstitution.create(this.var, newVar);
            for (int i = childDnf.size()-1; i >= 0; i--) {
                List<Itpf> conjClause = childDnf.get(i);
                for (int j = conjClause.size()-1; j >= 0; j--) {
                    conjClause.set(i, conjClause.get(i).applySubstitution(sigma));
                }
            }
        }
        quantors.add(new Pair<TRSVariable, Boolean>(newVar, this.isAll() ^ neg));
        return childDnf;
    }

    @Override
    protected final void collectFreeVariables(Set<TRSVariable> variables) {
        this.child.collectFreeVariables(variables);
        variables.remove(this.var);
    }

}

