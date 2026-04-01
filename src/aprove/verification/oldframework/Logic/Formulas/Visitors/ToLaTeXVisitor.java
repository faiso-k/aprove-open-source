package aprove.verification.oldframework.Logic.Formulas.Visitors ;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Syntax.*;


/** returns latex representation of this formula
 * Note: This visitor is obviously safe
 * @author  Eugen
 * @version $Id$
 */

public class ToLaTeXVisitor implements FineFormulaVisitor<StringBuffer> {

    static String TRUE_STRING         = "\\top";

    static String FALSE_STRING         = "\\bottom";

    protected StringBuffer             stringBuffer;

    public ToLaTeXVisitor(Formula formula) {
        this(formula,new LinkedHashSet<VariableSymbol>());
    }

    public ToLaTeXVisitor(Formula formula, Set<VariableSymbol> quantifiedVariables) {
        this(formula, quantifiedVariables, true);
    }

    public ToLaTeXVisitor(Formula formula, Set<VariableSymbol> quantifiedVariables, boolean allQuantified) {
        this.stringBuffer = new StringBuffer();

        Vector<AlgebraVariable> variables = new Vector<AlgebraVariable>(formula.getAllVariables());
        for(int i=0; i < variables.size(); i++) {
            if(quantifiedVariables.contains(variables.get(i).getVariableSymbol())) {
                if(! allQuantified){
                    this.stringBuffer.append("\\exists ");
                }
                else{
                    this.stringBuffer.append("\\forall ");
                }
            }
            this.stringBuffer.append(variables.get(i).getSymbol().getName());
            this.stringBuffer.append(":");
            this.stringBuffer.append(variables.get(i).getSymbol().getSort().getName());
            if( i < (variables.size()-1) ) {
                this.stringBuffer.append(",");
            }else {
                this.stringBuffer.append(".");
            }
        }
    }

    /**
     * returns the latex representation of this formula
     */
    public static String apply(Formula formula) {
        return "$"+formula.apply(new ToLaTeXVisitor(formula)).toString()+"$";
    }

    public static String apply(Formula formula, Set<VariableSymbol> allquantifiedVariables) {
        return "$"+formula.apply(new ToLaTeXVisitor(formula, allquantifiedVariables)).toString()+"$";
    }

    public static String apply(Formula formula, Set<VariableSymbol> quantifiedVariables, boolean allQuantified) {
        return "$"+formula.apply(new ToLaTeXVisitor(formula, quantifiedVariables, allQuantified)).toString()+"$";
    }

    @Override
    public StringBuffer caseEquation( Equation equation ) {

        this.stringBuffer.append( equation.getLeft().toLaTeX() );
        this.stringBuffer.append(" = ");
        this.stringBuffer.append( equation.getRight().toLaTeX() );

        return this.stringBuffer;
    }

    @Override
    public StringBuffer caseNot( Not not ) {

        this.stringBuffer.append(" \\lnot (");
        not.getLeft().apply(this);
        this.stringBuffer.append(")");

        return this.stringBuffer;
    }

    @Override
    public StringBuffer caseAnd( And and ) {

        this.stringBuffer.append("(");
        and.getLeft().apply(this);
        this.stringBuffer.append(" \\land ");
        and.getRight().apply(this);
        this.stringBuffer.append(")");

        return this.stringBuffer;

    }

    @Override
    public StringBuffer caseOr( Or or ){


        this.stringBuffer.append("(");
        or.getLeft().apply(this);
        this.stringBuffer.append(" \\lor ");
        or.getRight().apply(this);
        this.stringBuffer.append(")");

        return this.stringBuffer;

    }

    @Override
    public StringBuffer caseImplication( Implication implication ){

        this.stringBuffer.append("(");
        implication.getLeft().apply(this);
        this.stringBuffer.append("  \\rightarrow ");
        implication.getRight().apply(this);
        this.stringBuffer.append(")");

        return this.stringBuffer;

    }

    @Override
    public StringBuffer caseEquivalence( Equivalence equivalence ){

        this.stringBuffer.append("(");
        equivalence.getLeft().apply(this);
        this.stringBuffer.append("  \\equiv ");
        equivalence.getRight().apply(this);
        this.stringBuffer.append(")");

        return this.stringBuffer;

    }

    @Override
    public StringBuffer caseTruthValue( FormulaTruthValue truthValue ) {

        if (truthValue.getValue()) {

            this.stringBuffer.append(ToStringFormulaVisitor.TRUE_STRING);

        } else {

            this.stringBuffer.append(ToStringFormulaVisitor.FALSE_STRING);

        }

        return this.stringBuffer;
    }
}
