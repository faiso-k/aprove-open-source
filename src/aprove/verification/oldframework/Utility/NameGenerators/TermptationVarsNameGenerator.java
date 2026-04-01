package aprove.verification.oldframework.Utility.NameGenerators;

import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.Utility.*;

public class TermptationVarsNameGenerator implements NameGenerator {

    @Override
    public String getNewName(String old, FreshNameChecker fne) {
        String next = TermptationVarsNameGenerator.escape_primes("_" + old);
        return FreshNameGenerator.PROLOG_FUNCS.getNewName(next, fne);
    }

    static String escape_primes(String old) {
        StringBuffer temp = new StringBuffer();
        for (int i = 0; i < old.length(); i++) {
            char ch = old.charAt(i);
            switch (ch) {
                case '\'':
                    temp.append("0");
                    break;
                default:
                    temp.append(ch);
                break;
            }
        }
        return temp.toString();
    }
}