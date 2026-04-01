package aprove.verification.oldframework.Utility.NameGenerators;

import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.Utility.*;

public class TermptationFuncsNameGenerator implements
        NameGenerator {
    @Override
    public String getNewName(String old, FreshNameChecker fne) {
        String next1 = TermptationVarsNameGenerator.escape_primes(old);
        next1 = "'"+next1+"'";
        if (fne.isUnused(next1)) {
            return next1;
        }

        String next2;
        // try appending integers: x -> x0, x1, x2, ... x666
        // this must eventually succeed.
        int i = 1;
        next2 = next1.substring(0,next1.length()-1) + Integer.valueOf(i).toString()+"'";
        while (!fne.isUnused(next2)) {
            i++; // increment the name
            next2 = next1.substring(0,next1.length()-1) + Integer.valueOf(i).toString()+"'";
        }
        return next2;
    }
}