/**
 *
 */
package aprove.input.Programs.Strategy;

import java.io.*;
import java.util.*;

import immutables.*;

public class GenericExpression implements StrategyExpression {
    final String name;
    final Parameters params;
    final ExpressionList subexpressions;

    public GenericExpression(String name, Parameters params,
            List<StrategyExpression> spars) {
        this.name = name;
        if (params == null) {
            this.params = Parameters.EMPTY;
        } else {
            this.params = params;
        }
        this.subexpressions = new ExpressionList(ImmutableCreator.create(spars));
    }

    @Override
    public int getOneLineSize(int precedence) {
        int n = this.name.length();
        n += this.params.getOneLineSize(0);
        n += this.subexpressions.getOneLineSize(0);
        return n;
    }

    @Override
    public void print(Appendable ap, PrettyPrintState pps) throws IOException {
        boolean seperate =
            pps.getPosInLine() + this.getOneLineSize(pps.getPrecedence()) > pps.getMaxWidth();
        pps.append(ap, this.name);
        int oldindent = pps.getIndention();
        if (seperate) {
            pps.setIndention(pps.getIndention() + 4);
            if (pps.getPosInLine() + this.params.getOneLineSize(pps.getPrecedence()) > pps.getMaxWidth()) {
                pps.newLine(ap);
                pps.indent(ap);
            }
        }
        this.params.print(ap, pps);
        if (seperate && !this.subexpressions.getExps().isEmpty()) {
            pps.newLine(ap);
            pps.indent(ap);
        }
        this.subexpressions.print(ap, pps);
        pps.setIndention(oldindent);
    }

    @Override
    public <T> T accept(ExpressionVisitor<T> visitor) {
        return visitor.visit(this);
    }
}