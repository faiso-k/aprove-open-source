/**
 *
 */
package aprove.input.Programs.Strategy;

import java.io.*;

public class ComplexValue implements Value {
    final String identifier;
    final Parameters params;

    public ComplexValue(String identifier, Parameters params) {
        this.identifier = identifier;
        if (params == null) {
            this.params = Parameters.EMPTY;
        } else {
            this.params = params;
        }
    }

    public String getIdentifier() {
        return this.identifier;
    }

    public Parameters getParams() {
        return this.params;
    }

    @Override
    public int getOneLineSize(int precedence) {
        return this.identifier.length() + this.params.getOneLineSize(0);
    }

    @Override
    public void print(Appendable ap,
            PrettyPrintState pps) throws IOException {
        int i = pps.getIndention();
        boolean seperate =
            pps.getPosInLine() + this.getOneLineSize(pps.getPrecedence()) > pps.getMaxWidth();
        pps.append(ap, this.identifier);
        if (seperate) {
            pps.setIndention(pps.getIndention()+4);
            pps.newLine(ap);
            pps.indent(ap);
        }

        if (!this.params.getMap().isEmpty()) {
            this.params.print(ap, pps);
        }
        pps.setIndention(i);
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();
        this.toBuilder(builder);
        return builder.toString();
    }

    @Override
    public void toBuilder(StringBuilder target) {
        target.append(this.identifier);
        if (! this.params.params.isEmpty()) {
            this.params.toBuilder(target);
        }
    }

    @Override
    public <T> T accept(ValueVisitor<T> visitor) {
        return visitor.visit(this);
    }
}