package aprove.verification.oldframework.Utility.NameGenerators;

import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Generates a new name by uppercasing the old one.
 *
 * If the new name is not fresh, use another NameGenerator for making a fresh
 * name from it.
 */
public class UppercasingNameGenerator implements NameGenerator {

    private final NameGenerator ng;

    public UppercasingNameGenerator(NameGenerator ng) {
        this.ng = ng;
    }

    @Override
    public String getNewName(String old, FreshNameChecker fne) {
        String next = old.toUpperCase();
        if (fne.isUnused(old)) {
            return next;
        } else {
            return this.ng.getNewName(next, fne);
        }
    }

}
