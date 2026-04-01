package aprove.verification.idpframework.Core.Utility;

/**
 *
 * @author MP
 */
public class FreshNumberGenerator {

    private volatile int nextNumber;

    public FreshNumberGenerator(final int startFrom) {
        this.nextNumber = startFrom;
    }

    public synchronized int getFreshNumber() {
        return this.nextNumber++;
    }

    public synchronized void increaseTo(final int nextNumber) {
        if (nextNumber < this.nextNumber) {
            throw new IllegalStateException("already had higher numbers");
        }
        this.nextNumber = nextNumber;
    }

}
