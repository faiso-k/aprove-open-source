package aprove.strategies.ExecutableStrategies;

public class UnableToConnectToDatabaseException extends Exception {

    public UnableToConnectToDatabaseException() {
        super();
    }

    public UnableToConnectToDatabaseException(String message, Throwable cause) {
        super(message, cause);
    }

    public UnableToConnectToDatabaseException(String message) {
        super(message);
    }

    public UnableToConnectToDatabaseException(Throwable cause) {
        super(cause);
    }
}
