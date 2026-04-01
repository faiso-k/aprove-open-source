package aprove.verification.oldframework.Algebra.Terms.Visitors;

import aprove.verification.oldframework.Algebra.Terms.*;

/** Marks all variables
 * @author Eugen
 */

public class HighlightVarsInTerm extends ToStringVisitor implements CoarseGrainedTermVisitor {

    protected AlgebraVariable selectedVar;
    protected boolean useHTML = false;

    public HighlightVarsInTerm(AlgebraVariable v, boolean useHTML){
        super(false);
        this.useHTML=useHTML;
        this.selectedVar =v;
    }


    @Override
    public Object caseVariable(AlgebraVariable v) {
        if (v.equals(this.selectedVar)){
            if (this.useHTML){
                return "<FONT color=red>" + v.getName() + "</FONT>";
            }
            return " <" + v.getName() + "> ";
        }
        return v.getName();
    }

    public static String apply(AlgebraTerm t,AlgebraVariable v, boolean useHTML) {
        HighlightVarsInTerm visitor = new HighlightVarsInTerm(v,useHTML);
        return (String)t.apply(visitor);
    }

}
