/*
 * Created on 11.09.2004
 */
package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Syntax.*;


/**
 * @author rabe
 */
public class ToHTMLFormulaVisitor implements FineFormulaVisitor<StringBuffer> {

    static String TRUE_STRING         = "T";
    static String FALSE_STRING         = "F";

    protected StringBuffer            stringBuffer;

    public ToHTMLFormulaVisitor(Formula formula) {
        this(formula, new LinkedHashSet<VariableSymbol>());
    }

    public ToHTMLFormulaVisitor(Formula formula, Set<VariableSymbol> allquantifiedVariables ) {
        this(formula, allquantifiedVariables, true);
    }

    public ToHTMLFormulaVisitor(Formula formula, Set<VariableSymbol> quantifiedVariables, boolean allQuantified) {

        this.stringBuffer = new StringBuffer();

        Vector<AlgebraVariable> variables = new Vector<AlgebraVariable>(formula.getAllVariables());
        for(int i=0; i < variables.size(); i++) {
            if(quantifiedVariables.contains(variables.get(i).getVariableSymbol())) {
                if (! allQuantified){
                    this.stringBuffer.append("&#8707;");
                }
                else{
                    this.stringBuffer.append("&#8704;");
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
     * returns the string representation of this formula
     */
    public static String apply(Formula formula) {
        return formula.apply(new ToHTMLFormulaVisitor(formula)).toString();
    }

    public static String apply(Formula formula, Set<VariableSymbol> allquantifiedVariables) {
        return formula.apply(new ToHTMLFormulaVisitor(formula,allquantifiedVariables)).toString();
    }

    public static String apply(Formula formula, Set<VariableSymbol> quantifiedVariables, boolean allQuantified) {
        return formula.apply(new ToHTMLFormulaVisitor(formula, quantifiedVariables, allQuantified)).toString();
    }

    @Override
    public StringBuffer caseEquation( Equation equation ) {

        this.stringBuffer.append( equation.getLeft().toHTML() );
        this.stringBuffer.append("=");
        this.stringBuffer.append( equation.getRight().toHTML() );

        return this.stringBuffer;

    }

    @Override
    public StringBuffer caseNot( Not not ) {

        this.stringBuffer.append("&#172;(");
        not.getLeft().apply(this);
        this.stringBuffer.append(")");

        return this.stringBuffer;

    }

    @Override
    public StringBuffer caseAnd( And and ) {

        this.stringBuffer.append("(");
        and.getLeft().apply(this);
        this.stringBuffer.append("&#8743;");
        and.getRight().apply(this);
        this.stringBuffer.append(")");

        return this.stringBuffer;

    }

    @Override
    public StringBuffer caseOr( Or or ){

        this.stringBuffer.append("(");
        or.getLeft().apply(this);
        this.stringBuffer.append("&#8744;");
        or.getRight().apply(this);
        this.stringBuffer.append(")");

        return this.stringBuffer;

    }

    @Override
    public StringBuffer caseImplication( Implication implication ){

        this.stringBuffer.append("(");
        implication.getLeft().apply(this);
        this.stringBuffer.append("&#8594;");
        implication.getRight().apply(this);
        this.stringBuffer.append(")");

        return this.stringBuffer;

    }

    @Override
    public StringBuffer caseEquivalence( Equivalence equivalence ){

        this.stringBuffer.append("(");
        equivalence.getLeft().apply(this);
        this.stringBuffer.append("=");
        equivalence.getRight().apply(this);
        this.stringBuffer.append(")");

        return this.stringBuffer;

    }

    @Override
    public StringBuffer caseTruthValue( FormulaTruthValue truthValue ) {
        this.stringBuffer.append(truthValue.equals(FormulaTruthValue.TRUE) ? "True" : "False");
        return this.stringBuffer;
    }

}
