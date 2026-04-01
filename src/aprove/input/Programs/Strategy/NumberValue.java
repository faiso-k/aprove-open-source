/**
 *
 */
package aprove.input.Programs.Strategy;

import java.io.*;

public class NumberValue implements Value {
    final Integer value;
    public NumberValue(Integer value) {
        this.value = value;
    }
    @Override
    public int getOneLineSize(int precedence) {
        return this.value.toString().length();
    }
    @Override
    public void print(Appendable ap,
            PrettyPrintState pps) throws IOException {
        pps.append(ap, this.value.toString());
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();
        this.toBuilder(builder);
        return builder.toString();
    }

    @Override
    public void toBuilder(StringBuilder target) {
        target.append(this.value);
    }

    @Override
    public <T> T accept(ValueVisitor<T> visitor) {
        return visitor.visit(this);
    }
}