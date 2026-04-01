package aprove.verification.idpframework.Core.Utility;

import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.Utility.*;

/**
 *
 * @author MP
 */
public class IDPNamesGenerator implements NameGenerator {

    private final int ticks;
    private final int numberBase;
    private final char nuberSeparator = '.';

    public IDPNamesGenerator() {
        this(2, 0);
    }

    public IDPNamesGenerator(final int ticks, final int numberBase) {
        this.ticks = ticks;
        this.numberBase = numberBase;
    }

    @Override
    public String getNewName(final String old, final FreshNameChecker fne) {
        if (fne.isUnused(old)) {
            return old;
        }

        int ticksAtEnd = old.length() - 1;
        while (old.charAt(ticksAtEnd) == '\'') {
            ticksAtEnd --;
        }
        ticksAtEnd = old.length() - ticksAtEnd - 1;

        final int numberIndex = old.lastIndexOf(this.nuberSeparator);
        int lastNumber = -1;
        String unnumberedPrefix = null;
        if (numberIndex > 0) {
            try {
                lastNumber = Integer.parseInt(old.substring(numberIndex + 1));
                unnumberedPrefix = old.substring(0, numberIndex + 1);
            } catch (final NumberFormatException e) {
            }
        }

        if (lastNumber < 0) {
            String ticked = old;
            for (int i = ticksAtEnd; i < this.ticks; i++) {
                ticked += "'";
                if (fne.isUnused(ticked)) {
                    return ticked;
                }
            }
        }

        if (lastNumber < 0) {
            lastNumber = this.numberBase - 1;
            unnumberedPrefix = old.substring(0, old.length() - ticksAtEnd) + String.valueOf(this.nuberSeparator);
        }

        for (int i = lastNumber + 1; ; i++) {
            final String numbered = unnumberedPrefix + i;
            if (fne.isUnused(numbered)) {
                return numbered;
            }
        }
    }

}
