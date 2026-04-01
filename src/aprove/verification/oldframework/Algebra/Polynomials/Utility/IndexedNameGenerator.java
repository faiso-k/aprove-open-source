package aprove.verification.oldframework.Algebra.Polynomials.Utility;

/**
 * Lightweight generator for up to 2^32 names of the form prefix + index.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class IndexedNameGenerator {

    private int currentIndex;
    private final String prefix;

    public IndexedNameGenerator(String prefix) {
        this.currentIndex = 0;
        this.prefix = prefix;
    }

    public String next() {
        return this.prefix + ++this.currentIndex;
    }

    @Override
    public String toString() {
        return "Prefix: " + this.prefix + " Last index: " + this.currentIndex;
    }
}
