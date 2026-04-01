package aprove.verification.oldframework.Syntax;

/**
 * used by SignatureTranslation
 * @author Christian Kaeunicke
 */

public class BijectivityViolation extends RuntimeException {
    public BijectivityViolation() {
    super();
    };

    public BijectivityViolation(String msg) {
    super(msg);
    };
};
