package aprove.verification.oldframework.Utility.NameGenerators;

import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.Utility.*;

public class SemlabVarsNameGenerator implements NameGenerator {

    @Override
    public String getNewName(String old, FreshNameChecker fne) {
        String next;
        if(fne.isUnused("|i|")) {
            return "|i|";
        }
        if(fne.isUnused("|j|")) {
            return "|j|";
        }
        if(fne.isUnused("|k|")) {
            return "|k|";
        }
        if(fne.isUnused("|l|")) {
            return "|l|";
        }
        if(fne.isUnused("|m|")) {
            return "|m|";
        }
        if(fne.isUnused("|n|")) {
            return "|n|";
        }
        if(fne.isUnused("|o|")) {
            return "|o|";
        }
        int i=1;
        next = old = "|p|1";
        while(!fne.isUnused(next)) {
            i++; // increment the name
            next = old.substring(0,old.length()-1) + i;
        }
        return next;
    }

}
