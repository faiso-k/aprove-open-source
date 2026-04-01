package aprove.verification.oldframework.Logic;

public class InvalidTruthValueException extends RuntimeException {

    public InvalidTruthValueException(Class<? extends TruthValue> clazz,
            TruthValue other) {
        super("Expected truth value of class " + clazz.getSimpleName() + ", but got " + other + " of class " + other.getClass().getSimpleName());
    }

}
