package aprove.verification.oldframework.SMT.Solver.Z3;

@SuppressWarnings("serial")
public class SMTFeatureUnavailableException extends Exception {

    public SMTFeatureUnavailableException() {
        super();
    }

    public SMTFeatureUnavailableException(String reason) {
        super(reason);
    }

}
