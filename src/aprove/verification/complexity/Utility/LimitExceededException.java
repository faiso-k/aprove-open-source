package aprove.verification.complexity.Utility;

public class LimitExceededException extends Exception {
    public LimitExceededException(String reason) {
        super(reason);
    }
}
