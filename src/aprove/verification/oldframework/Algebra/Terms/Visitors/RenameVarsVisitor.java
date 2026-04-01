package aprove.verification.oldframework.Algebra.Terms.Visitors ;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Utility.*;

/** Renames all vars in a term.
 * @author Burak Emir, Peter Schneider-Kamp
 * @version $Id$
 */
public class RenameVarsVisitor extends CoarseGrainedDepthFirstTermVisitor {

    protected FreshVarGenerator fg;

    @Override
    public void inVariable(AlgebraVariable v) {
        // if v is fresh, then nothing changes
        AlgebraVariable x = this.fg.getFreshVariable(v, true);
        v.rename(x.getVariableSymbol());
    }

    public RenameVarsVisitor(Set<AlgebraVariable> sv) {
        this.fg = new FreshVarGenerator(sv);
    }

    public RenameVarsVisitor(FreshVarGenerator fg) {
        this.fg = fg;
    }

}
