package aprove.verification.oldframework.Utility.NameGenerators;

import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Generates a new name suitable for ACL2
 *
 * If the new name is not fresh, use another NameGenerator for making a fresh
 * name from it.
 */
public class ACL2NameGenerator implements NameGenerator {

    private final NameGenerator ng = new AppendNameGenerator(0,1);

    @Override
    public String getNewName(String old, FreshNameChecker fne) {
        String next = "trs_"+old.replace("'", "prime");
        if (fne.isUnused(old)) {
            return next;
        } else {
            return this.ng.getNewName(next, fne);
        }
    }

}
