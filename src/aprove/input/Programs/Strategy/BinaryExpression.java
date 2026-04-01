package aprove.input.Programs.Strategy;

import java.io.*;

public class BinaryExpression extends GenericExpression {
    private final String operator;

    public BinaryExpression(String name, String operator, StrategyExpression e1, StrategyExpression e2) {
        super(name, Parameters.EMPTY, Utils.createFixedImmutableArrayList(e1, e2));
        this.operator = operator;
    }

    protected String getOperatorName() {
        return this.operator;
    }

    private void printTail(Appendable ap,
            PrettyPrintState pps,
            BinaryExpression bexp) throws IOException {
        StrategyExpression e1 = bexp.subexpressions.getExps().get(0);
        StrategyExpression e2 = bexp.subexpressions.getExps().get(1);
        e1.print(ap, pps);
        pps.newLine(ap);
        pps.indent(ap);
        pps.append(ap, bexp.getOperatorName() + " ");
        if (e2 instanceof BinaryExpression) {
            this.printTail(ap, pps, (BinaryExpression) e2);
        } else {
            e2.print(ap, pps);
        }
    }

    @Override
    public void print(Appendable ap, PrettyPrintState pps) throws IOException {
        StrategyExpression e1 = this.subexpressions.getExps().get(0);
        StrategyExpression e2 = this.subexpressions.getExps().get(1);
        boolean needParens = pps.getPrecedence() > 2;
        boolean seperate =
            pps.getPosInLine() + this.getOneLineSize(pps.getPrecedence()) > pps.getMaxWidth();
        if (needParens) {
            pps.append(ap, "(");
        }
        int oldindent = pps.getIndention();
        pps.setIndention(pps.getPosInLine());
        pps.setPrecedence(3);
        if (seperate) {
            pps.append(ap, "  ");
        }
        e1.print(ap, pps);
        if (seperate) {
            pps.newLine(ap);
            pps.indent(ap);
            pps.append(ap, this.getOperatorName() + " ");
        } else {
            pps.append(ap, " " + this.getOperatorName() + " ");
        }
        pps.setPrecedence(2);
        if (seperate && e2 instanceof BinaryExpression) {
            this.printTail(ap, pps, (BinaryExpression) e2);
        } else {
            e2.print(ap, pps);
        }
        if (needParens) {
            pps.append(ap, ")");
        }
        pps.setIndention(oldindent);
    }

    @Override
    public int getOneLineSize(int precedence) {
        boolean needParens = precedence > 2;
        int n =
            (2 + this.getOperatorName().length())
                * this.subexpressions.getExps().size();
        boolean first = true;
        for (StrategyExpression e : this.subexpressions.getExps()) {
            if (first) {
                first = false;
                n += e.getOneLineSize(3);
            } else {
                n += e.getOneLineSize(2);
            }
        }
        return needParens ? n + 5 : n + 3;
    }
}
