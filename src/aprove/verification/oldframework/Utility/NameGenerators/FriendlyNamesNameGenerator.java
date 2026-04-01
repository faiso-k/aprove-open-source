package aprove.verification.oldframework.Utility.NameGenerators;

import java.util.*;

import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.Utility.*;

public class FriendlyNamesNameGenerator implements
        NameGenerator {
    public enum Mode {FRIENDLY, CiME, TTT}

    /**
     * Wraps a FreshNameEnsurerInterface and additionally disallows
     * names contained in cime_invalid
     */
    private class CimeFNEIWrapper implements FreshNameChecker {

        private final FreshNameChecker fne;

        public CimeFNEIWrapper(FreshNameChecker fne) {
            this.fne = fne;
        }

        @Override
        public boolean isUnused(String name) {
            if (FriendlyNamesNameGenerator.this.mode == Mode.CiME && FriendlyNamesNameGenerator.cime_invalid.contains(name)) {
                /* reserved keyword in CiME */
                return false;
            }
            return this.fne.isUnused(name);
        }

    }

    private static final AppendNameGenerator ang =
        new AppendNameGenerator(2, 1);
    private static final HashMap<String,String> specialchars;
    private static final Set<String> ttt_specialchars;
    private static final Set<String> cime_specialchars;
    private static final Set<String> cime_invalid;

    static {
        specialchars = new HashMap<String,String>();
        FriendlyNamesNameGenerator.specialchars.put("+","plus");
        FriendlyNamesNameGenerator.specialchars.put("-","minus");
        FriendlyNamesNameGenerator.specialchars.put("*","times");
        FriendlyNamesNameGenerator.specialchars.put(":","cons");
        FriendlyNamesNameGenerator.specialchars.put(".","dot");
        FriendlyNamesNameGenerator.specialchars.put("/","div");
        FriendlyNamesNameGenerator.specialchars.put("\\","vid");
        FriendlyNamesNameGenerator.specialchars.put("=","eq");
        FriendlyNamesNameGenerator.specialchars.put("|","pipe");
        FriendlyNamesNameGenerator.specialchars.put("@","app");
        FriendlyNamesNameGenerator.specialchars.put("<","lt");
        FriendlyNamesNameGenerator.specialchars.put(">","gr");
        FriendlyNamesNameGenerator.specialchars.put("#","sharp");
        FriendlyNamesNameGenerator.specialchars.put("^","power");
        FriendlyNamesNameGenerator.specialchars.put("&","and");
        FriendlyNamesNameGenerator.specialchars.put("%","percent");
        FriendlyNamesNameGenerator.specialchars.put(":","colon");
        FriendlyNamesNameGenerator.specialchars.put("!","mark");
        FriendlyNamesNameGenerator.specialchars.put("$","dollar");
        FriendlyNamesNameGenerator.specialchars.put("?","what");
        FriendlyNamesNameGenerator.specialchars.put("(","open");
        FriendlyNamesNameGenerator.specialchars.put(")","close");
        FriendlyNamesNameGenerator.specialchars.put(";","semicolon");
        FriendlyNamesNameGenerator.specialchars.put(",","comma");
        ttt_specialchars = new HashSet<String>();
        FriendlyNamesNameGenerator.ttt_specialchars.add("+");
        FriendlyNamesNameGenerator.ttt_specialchars.add("-");
        FriendlyNamesNameGenerator.ttt_specialchars.add("*");
        FriendlyNamesNameGenerator.ttt_specialchars.add(":");
        FriendlyNamesNameGenerator.ttt_specialchars.add(".");
        FriendlyNamesNameGenerator.ttt_specialchars.add("\\");
        FriendlyNamesNameGenerator.ttt_specialchars.add("/");
        FriendlyNamesNameGenerator.ttt_specialchars.add("=");
        FriendlyNamesNameGenerator.ttt_specialchars.add("|");
        FriendlyNamesNameGenerator.ttt_specialchars.add("@");
        FriendlyNamesNameGenerator.ttt_specialchars.add("<");
        FriendlyNamesNameGenerator.ttt_specialchars.add(">");
        cime_specialchars = new HashSet<String>();
        FriendlyNamesNameGenerator.cime_specialchars.add("^");
        FriendlyNamesNameGenerator.cime_specialchars.add("+");
        FriendlyNamesNameGenerator.cime_specialchars.add(".");
        FriendlyNamesNameGenerator.cime_specialchars.add("&");
        FriendlyNamesNameGenerator.cime_specialchars.add("*");
        FriendlyNamesNameGenerator.cime_specialchars.add("-");
        FriendlyNamesNameGenerator.cime_specialchars.add("/");
        FriendlyNamesNameGenerator.cime_specialchars.add("?");
        FriendlyNamesNameGenerator.cime_specialchars.add("!");
        FriendlyNamesNameGenerator.cime_specialchars.add("@");
        FriendlyNamesNameGenerator.cime_specialchars.add("~");
        FriendlyNamesNameGenerator.cime_specialchars.add("#");
        FriendlyNamesNameGenerator.cime_specialchars.add("|");
        FriendlyNamesNameGenerator.cime_specialchars.add(":");
        FriendlyNamesNameGenerator.cime_specialchars.add("%");
        FriendlyNamesNameGenerator.cime_specialchars.add("$");
        FriendlyNamesNameGenerator.cime_specialchars.add("<");
        FriendlyNamesNameGenerator.cime_specialchars.add("=");
        FriendlyNamesNameGenerator.cime_specialchars.add(">");
        FriendlyNamesNameGenerator.cime_specialchars.add("#");
        cime_invalid = new HashSet<String>();
        FriendlyNamesNameGenerator.cime_invalid.add("constant");
        FriendlyNamesNameGenerator.cime_invalid.add("unary");
        FriendlyNamesNameGenerator.cime_invalid.add("binary");
        FriendlyNamesNameGenerator.cime_invalid.add("infix");
        FriendlyNamesNameGenerator.cime_invalid.add("prefix");
        FriendlyNamesNameGenerator.cime_invalid.add("postfix");
        FriendlyNamesNameGenerator.cime_invalid.add("commutative");
        FriendlyNamesNameGenerator.cime_invalid.add("AC");
        FriendlyNamesNameGenerator.cime_invalid.add(":");
        FriendlyNamesNameGenerator.cime_invalid.add("->");
        FriendlyNamesNameGenerator.cime_invalid.add("<");
        FriendlyNamesNameGenerator.cime_invalid.add(">");
        FriendlyNamesNameGenerator.cime_invalid.add("=");
        FriendlyNamesNameGenerator.cime_invalid.add("<=");
        FriendlyNamesNameGenerator.cime_invalid.add(">=");
        FriendlyNamesNameGenerator.cime_invalid.add("<>");
        FriendlyNamesNameGenerator.cime_invalid.add("mul");
    }

    private FriendlyNamesNameGenerator.Mode mode;

    public FriendlyNamesNameGenerator(FriendlyNamesNameGenerator.Mode m) {
        this.mode = m;
    }

    @Override
    public String getNewName(String old, FreshNameChecker fne) {
        String s = "";
        String safe_s = "";
        String next = old;
        for (int i = 0; i < next.length(); i++) {
            char c = next.charAt(i);
            String rs = FriendlyNamesNameGenerator.specialchars.get(Character.valueOf(c).toString());
            s += (rs == null
                    || (this.mode == Mode.TTT
                            && !FriendlyNamesNameGenerator.ttt_specialchars.contains(Character.valueOf(c).toString()))
                    || (this.mode == Mode.CiME &&
                            !FriendlyNamesNameGenerator.cime_specialchars.contains(Character.valueOf(c).toString()))
                 ) ? Character.valueOf(c).toString() : rs;

            safe_s += (rs == null) ? Character.valueOf(c).toString() : rs;
        }
        if (this.mode == Mode.CiME && FriendlyNamesNameGenerator.cime_invalid.contains(s)) {
            next = safe_s;
        }
        else {
            next = s;
        }

        if (this.mode == Mode.CiME) {
            fne = new CimeFNEIWrapper(fne);
        }

        if (fne.isUnused(next)) {
            return next;
        }

        return FriendlyNamesNameGenerator.ang.getNewName(next, fne);
    }

}