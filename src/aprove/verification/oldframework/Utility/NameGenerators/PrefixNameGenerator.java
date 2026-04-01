package aprove.verification.oldframework.Utility.NameGenerators;

import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.Utility.*;

public class PrefixNameGenerator implements NameGenerator {

    private final String prefix;
    private int count = 0;

    public PrefixNameGenerator(String prefix) {
        this.prefix = prefix;
    }

    @Override
    public String getNewName(String old, FreshNameChecker fne) {
        // FIXME: Add Something like max-tries?
        String name;
        do {
            name = this.prefix + (this.count++);
        } while (!fne.isUnused(name));
        return name;
    }

}
