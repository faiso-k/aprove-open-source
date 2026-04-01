/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.DPProblem.SMT_LIA;

public enum ArithmeticRelation {
    LT("<"), LE("<="), EQ("="), GT(">"), GE(">=");

    private final String repr;

    ArithmeticRelation(String repr) {
        this.repr = repr;
    }

    public String getRepr() {
        return this.repr;
    }
}
