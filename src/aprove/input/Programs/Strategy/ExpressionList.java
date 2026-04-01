package aprove.input.Programs.Strategy;

import java.io.*;

import immutables.*;

public class ExpressionList implements PrettyPrintable, VisitableStrategyElement {
    final ImmutableList<StrategyExpression> exps;

    public ExpressionList(ImmutableList<StrategyExpression> immutableList) {
        if (immutableList == null) {
            this.exps = Utils.createFixedImmutableArrayList();
        } else {
            this.exps = immutableList;
        }
    }

    @Override
    public int getOneLineSize(int precedence) {
        if (this.getExps().isEmpty()) {
            return 0;
        }
        int n = 2 + 2 * (this.getExps().size() - 1);
        for (StrategyExpression e : this.getExps()) {
            n += e.getOneLineSize(0);
        }
        return n;
    }

    @Override
    public void print(Appendable ap, PrettyPrintState pps) throws IOException {
        if (this.exps.isEmpty()) {
            return;
        }

        boolean seperate =
            pps.getPosInLine() + this.getOneLineSize(pps.getPrecedence()) > pps.getMaxWidth();
        boolean seperateHere = seperate && this.exps.size() > 1;
        int oldindent = pps.getIndention();
        pps.append(ap, "(");
        if (seperateHere) {
            pps.setIndention(pps.getPosInLine() - 1);
        }
        boolean first = true;
        for (StrategyExpression e : this.getExps()) {
            if (first) {
                first = false;
            } else {
                if (seperateHere) {
                    pps.newLine(ap);
                    pps.indent(ap);
                }
                pps.append(ap, ",");
            }
            pps.setPrecedence(0);
            e.print(ap, pps);
        }

        if (seperate) {
            pps.newLine(ap);
            pps.indent(ap);
        }
        pps.append(ap, ")");
        pps.setIndention(oldindent);
    }

    public ImmutableList<StrategyExpression> getExps() {
        return this.exps;
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();
        this.toBuilder(builder);
        return builder.toString();
    }

    public void toBuilder(StringBuilder target) {
        target.append("(");
        for(StrategyExpression e: this.exps) {
            target.append(e);
            target.append(", ");
        }
        if (! this.exps.isEmpty()) {
            target.delete(target.length()-2, target.length());
        }
        target.append(")");
    }

    @Override
    public void accept(StrategyElementVisitor visitor) {
        visitor.visit(this);
    }
}
