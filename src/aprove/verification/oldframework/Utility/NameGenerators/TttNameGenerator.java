package aprove.verification.oldframework.Utility.NameGenerators;

import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.Utility.*;

public class TttNameGenerator implements
        NameGenerator {
    @Override
    public String getNewName(String old, FreshNameChecker fne) {
        switch (old.charAt(0)) {
            case '+': old = "plus";
                break;
            case '-': old = "minus";
                break;
            case '*': old = "times";
                break;
            case ':': old = "cons";
                break;
            case '.': old = "op";
                break;
            case '\\': old = "vid";
                break;
            case '/': old = "div";
                break;
            case '=': old = "eq";
                break;
            case '|': old = "parallel";
                break;
            case '@': old = "at";
                break;
            case '<': old = "lt";
                break;
            case '>': old = "gt";
                break;
        }
        if (fne.isUnused(old)) {
            return old;
        }
        return FreshNameGenerator.PROLOG_FUNCS.getNewName(old, fne);
    }
}