package aprove.input.Programs.Strategy;

import java.io.*;

public class PostfixExpression extends GenericExpression {
    private final String operator;

    public PostfixExpression(String name, String operator, StrategyExpression exp) {
        super(name, Parameters.EMPTY, Utils.createFixedImmutableArrayList(exp));
        this.operator = operator;
    }

    protected String getOperatorName() {
        return this.operator;
    }

    @Override
    public void print(Appendable ap, PrettyPrintState pps) throws IOException {
        boolean needParens = pps.getPrecedence() > 3;
        if (needParens) {
            pps.append(ap, "(");
        }
        pps.setPrecedence(3);
        this.subexpressions.getExps().get(0).print(ap, pps);
        pps.append(ap, this.getOperatorName());
        if (needParens) {
            pps.append(ap, ")");
        }
    }

    @Override
    public int getOneLineSize(int precedence) {
        boolean needParens = precedence > 3;
        int n = this.subexpressions.getExps().get(0).getOneLineSize(3);
        return needParens ? n + 3 : n + 1;
    }
}
