/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

public abstract class ItpfUnary extends Itpf {

    protected final Itpf child;

    public ItpfUnary(Itpf child, boolean isNormalized, boolean isDnf) {
        super(isNormalized, isDnf);
        this.child = child;
    }

    public Itpf getChild() {
        return this.child;
    }

    @Override
    protected void collectFreeVariables(Set<TRSVariable> variables) {
        this.child.collectFreeVariables(variables);
    }

    @Override
    protected void collectFunctionSymbols(Set<FunctionSymbol> fs) {
        this.child.collectFunctionSymbols(fs);
    }

}
