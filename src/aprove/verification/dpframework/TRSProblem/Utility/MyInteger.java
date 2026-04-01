package aprove.verification.dpframework.TRSProblem.Utility;

/**
 * class encapsulating a primitive Int-Value and enabling SIDE-EFFECTS to its instances
 *
 * @author Sebastian Weise
 */
public class MyInteger {
    private int intValue;

    public MyInteger(final int intValue) {
        this.intValue = intValue;
    }

    public int getIntValue() {
        return this.intValue;
    }

    public void setIntValue(final int intValue) {
        this.intValue = intValue;
    }

    public void increase() {
        this.intValue++;
    }

    public void decrease() {
        this.intValue--;
    }
}