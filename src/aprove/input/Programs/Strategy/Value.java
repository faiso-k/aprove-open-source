/**
 *
 */
package aprove.input.Programs.Strategy;

public interface Value extends PrettyPrintable {
    public void toBuilder(StringBuilder target);

    public <T> T accept(ValueVisitor<T> visitor);
}