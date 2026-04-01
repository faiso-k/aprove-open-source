/**
 *
 */
package aprove.input.Programs.Strategy;

import java.io.*;

public class LetDeclaration extends Declaration {
    final StrategyExpression body;

    public LetDeclaration(String name, StrategyExpression body) {
        super(name);
        assert (body != null);
        this.body = body;
    }

    @Override
    public void print(Appendable ap) throws IOException {
        PrettyPrintState pps = new PrettyPrintState();
        pps.append(ap, "let " + this.name + " = ");
        pps.setPrecedence(0);
        this.body.print(ap, pps);
    }

    @Override
    public void accept(DeclarationVisitor visitor) {
        visitor.visit(this);
    }
}