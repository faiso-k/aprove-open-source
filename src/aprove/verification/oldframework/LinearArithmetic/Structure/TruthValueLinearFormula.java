package aprove.verification.oldframework.LinearArithmetic.Structure;


/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class TruthValueLinearFormula extends LinearFormula{

    public static final TruthValueLinearFormula TRUE = TruthValueLinearFormula.create(true);
    public static final TruthValueLinearFormula FALSE = TruthValueLinearFormula.create(false);

    protected boolean b;
    private final int hashCode;

    public TruthValueLinearFormula( boolean b ) {
        this.b = b;
        this.hashCode = b ? 0 : 1;
    }

    public static TruthValueLinearFormula create(boolean b) {
        return new TruthValueLinearFormula( b );
    }

    @Override
    public <T> T apply(LinearFormulaVisitor<T> fv) {
        return fv.caseTruthValue( this );
    }

    @Override
    public LinearFormula deepcopy() {
        return new TruthValueLinearFormula(this.b);
    }

    public boolean getValue(){
        return this.b;
    }

    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();

        sb.append(this.b);

        return sb.toString();
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    @Override
    public boolean equals(Object object) {

        if( object instanceof TruthValueLinearFormula ) {

            TruthValueLinearFormula truthValue = (TruthValueLinearFormula)object;

            return ( this.b == truthValue.b );
        }
        else {
            return false;
        }
    }

}
