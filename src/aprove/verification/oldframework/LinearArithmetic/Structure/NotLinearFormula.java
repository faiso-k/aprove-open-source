package aprove.verification.oldframework.LinearArithmetic.Structure;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class NotLinearFormula extends LinearFormula{
    protected LinearFormula subFormula;

    public NotLinearFormula(LinearFormula subFormula) {
        this.subFormula = subFormula;
    }

    @Override
    final public <T> T apply(LinearFormulaVisitor<T> fv) {
        return fv.caseNot( this );
    }

    @Override
    public LinearFormula deepcopy() {
        return new NotLinearFormula(this.subFormula.deepcopy());
    }

    /**
     * @return the subForumla
     */
    public LinearFormula getSubFormula() {
        return this.subFormula;
    }

    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();

        sb.append("~ ( ");
        sb.append(this.subFormula);
        sb.append(" ) ");

        return sb.toString();
    }
}
