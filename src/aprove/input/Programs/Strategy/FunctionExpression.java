/**
 *
 */
package aprove.input.Programs.Strategy;

import java.io.*;

public class FunctionExpression implements StrategyExpression {
    final String name;
    // final Parameters params; // ignored for now

    public FunctionExpression(String name /*, Parameters params */) {
        this.name = name;
//        this.params = params;
    }

    @Override
    public void print(Appendable ap,
            PrettyPrintState pps) throws IOException {
        pps.append(ap, this.name);
    }

    @Override
    public int getOneLineSize(int precedence) {
        return this.name.length();
    }

    @Override
    public <T> T accept(ExpressionVisitor<T> visitor) {
        return visitor.visit(this);
    }
}