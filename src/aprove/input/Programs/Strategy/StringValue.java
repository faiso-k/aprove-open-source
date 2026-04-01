/**
 *
 */
package aprove.input.Programs.Strategy;

import java.io.*;

public class StringValue implements Value {
    final String value;
    public StringValue(String value) {
        this.value = value;
    }
    @Override
    public int getOneLineSize(int precedence) {
        return 2 + this.value.length();
    }
    @Override
    public void print(Appendable ap,
            PrettyPrintState pps) throws IOException {
        pps.append(ap, "\"");
        pps.append(ap, this.value);
        pps.append(ap, "\"");
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder(this.value.length() + 2);
        this.toBuilder(builder);
        return builder.toString();
    }

    @Override
    public void toBuilder(StringBuilder target) {
        target.append('"');
        target.append(this.value);
        target.append('"');
    }

    @Override
    public <T> T accept(ValueVisitor<T> visitor) {
        return visitor.visit(this);
    }
}