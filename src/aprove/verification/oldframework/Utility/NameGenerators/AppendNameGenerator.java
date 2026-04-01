package aprove.verification.oldframework.Utility.NameGenerators;

import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Generates new names for a old name by adding single quotes or numbers.
 *
 * If the name is already fresh, just return it.
 * Else try appending a number of single quotes,
 * else try appending (increasing) numbers instead.
 */
public class AppendNameGenerator implements NameGenerator {

    private final int ticks;
    private final int start;

    /**
     * @param ticks
     *            Try appending up to <code>ticks</code> single quotes
     * @param start
     *            If appending integers, start at <code>start</code>.
     */
    public AppendNameGenerator(int ticks, int start) {
        this.ticks = ticks;
        this.start = start;
    }

    @Override
    public String getNewName(String old, FreshNameChecker fne) {
        if (fne.isUnused(old)) {
            return old;
        }

        String name = old;
        for (int ticks = 0; ticks < this.ticks; ticks++) {
            name = name + "'";
            if (fne.isUnused(name)) {
                return name;
            }
        }

        int count = this.start;
        do {
            name = old + (count++);
        } while (!fne.isUnused(name));
        return name;
    }

}
