package aprove.strategies.ExecutableStrategies;


public class Fail extends ExecutableStrategy {

    public static final Fail Fail = new Fail("no reason");

    private final String reason;

    public Fail(String reason) {
        super(null);
        this.reason = reason;
    }

    public Fail(String reason, Fail originalFail) {
        this(reason + ": " + originalFail.reason);
    }

    @Override
    public boolean isNormal() {
        return true;
    }

    @Override
    public boolean isFail() {
        return true;
    }

    @Override
    ExecutableStrategy exec()  {
        throw new RuntimeException("You should not execute Fail");
    }

    @Override
    void stop(String reason) {
    }

    @Override
    public String toString() {
        return "Fail(" + this.reason + ")";
    }


}
