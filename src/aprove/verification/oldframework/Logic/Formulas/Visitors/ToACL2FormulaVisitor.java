/*
 * Created on 11.09.2004
 */
package aprove.verification.oldframework.Logic.Formulas.Visitors;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author nowonder
 */
public class ToACL2FormulaVisitor implements FineFormulaVisitor<StringBuffer> {

    static String TRUE_STRING = "T";
    static String FALSE_STRING = "NIL";
    static String INDENT_STRING = "  ";

    protected StringBuffer sb;
    protected int indent;
    protected FreshNameGenerator fng;
    protected boolean fullLists;

    public ToACL2FormulaVisitor(StringBuffer sb, int indent, FreshNameGenerator fng, boolean fullLists) {
        this.sb = sb;
        this.indent = indent;
        this.fng = fng;
        this.fullLists = fullLists;
    }

    public void init(Formula formula) {
        this.indent("defthm test");
        // define is-sort function for all sorts
        this.indent("implies");
        this.preindent("and");
        for (AlgebraVariable var : formula.getAllVariables()) {
            this.level();
            this.sb.append("(");
            this.sb.append(this.fng.getFreshName("is"+var.getSort().getName(),true));
            this.sb.append(" ");
            this.sb.append(this.fng.getFreshName(var.getName(),true));
            this.sb.append(")");
        }
        this.dedent();
        this.level();
    }

    public void deinit(boolean noGeneralize) {
        this.dedent();
        if (noGeneralize) {
            this.level();
            this.sb.append(":hints ((\"Goal\" :do-not '(generalize)))");
        }
        this.dedent();
    }

    private void indent(String head) {
        this.preindent(head);
        this.level();
    }

    private void preindent(String head) {
        this.sb.append("(");
        this.sb.append(head);
        this.indent++;
    }

    private void dedent() {
        this.indent--;
        this.level();
        this.sb.append(")");
    }

    private void level() {
        this.sb.append("\n");
        for (int i = 0; i < this.indent; i++) {
            this.sb.append(ToACL2FormulaVisitor.INDENT_STRING);
        }
    }

    /**
     * returns the string representation of this formula
     */
    public static void apply(Formula formula, StringBuffer sb, int indent, FreshNameGenerator fng, boolean fullLists, boolean noGeneralize) {
        ToACL2FormulaVisitor visitor = new ToACL2FormulaVisitor(sb, indent, fng, fullLists);
        visitor.init(formula);
        formula.apply(visitor);
        visitor.deinit(noGeneralize);
    }

    @Override
    public StringBuffer caseEquation( Equation equation ) {
        this.indent("eq");
        equation.getLeft().toACL2(this.sb, this.indent, this.fng, null, this.fullLists);
        this.level();
        equation.getRight().toACL2(this.sb, this.indent, this.fng, null, this.fullLists);
        this.dedent();
        return this.sb;
    }

    @Override
    public StringBuffer caseNot( Not not ) {
        this.indent("not");
        not.getLeft().apply(this);
        this.dedent();
        return this.sb;
    }

    @Override
    public StringBuffer caseAnd( And and ) {
        this.indent("and");
        and.getLeft().apply(this);
        this.level();
        and.getRight().apply(this);
        this.dedent();
        return this.sb;
    }

    @Override
    public StringBuffer caseOr( Or or ){
        this.indent("or");
        or.getLeft().apply(this);
        this.level();
        or.getRight().apply(this);
        this.dedent();
        return this.sb;
    }

    @Override
    public StringBuffer caseImplication( Implication implication ){
        this.indent("implies");
        implication.getLeft().apply(this);
        this.level();
        implication.getRight().apply(this);
        this.dedent();
        return this.sb;
    }

    @Override
    public StringBuffer caseEquivalence( Equivalence equivalence ){
        this.indent("equivalent");
        equivalence.getLeft().apply(this);
        this.level();
        equivalence.getRight().apply(this);
        this.dedent();
        return this.sb;
    }

    @Override
    public StringBuffer caseTruthValue( FormulaTruthValue truthValue ) {
        if (truthValue.getValue()) {
            this.sb.append(ToStringFormulaVisitor.TRUE_STRING);
        } else {
            this.sb.append(ToStringFormulaVisitor.FALSE_STRING);
        }
        return this.sb;
    }

}
