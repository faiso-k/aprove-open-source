/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;


public abstract class ItpfNAry extends Itpf {

    protected final ImmutableSet<? extends Itpf> children;

    public ItpfNAry(ImmutableSet<? extends Itpf> children, boolean isNormalized, boolean isDnf) {
        super(isNormalized, isDnf);
        this.children = children;
    }


    public ImmutableSet<? extends Itpf> getChildren() {
        return this.children;
    }

    @Override
    protected void collectFreeVariables(Set<TRSVariable> variables) {
        for (Itpf child : this.children) {
            child.collectFreeVariables(variables);
        }
    }

    @Override
    protected void collectFunctionSymbols(Set<FunctionSymbol> fs) {
        for (Itpf child : this.children) {
            child.collectFunctionSymbols(fs);
        }
    }

}
