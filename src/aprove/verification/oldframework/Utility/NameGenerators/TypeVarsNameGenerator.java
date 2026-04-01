package aprove.verification.oldframework.Utility.NameGenerators;

import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.Utility.*;

public class TypeVarsNameGenerator implements
        NameGenerator {
    @Override
    public String getNewName(String old, FreshNameChecker fne) {
        String next = old;
        while (!fne.isUnused(next)) {
            char c = next.charAt(old.length()-1);
            if (c == 'z') {
                next = next + "a";
            } else {
                c++;
                next = next.substring(0,old.length()-1) + c;
            }
        }
        return next;
    }
}