package aprove.input.Programs.prolog;

import java.util.*;

/**
 * @author cryingshadow
 * @version $Id$
 */
public class PrologOperatorSet {

    /**
     * We have 7 different fixities enumerated here.
     */
    public static final int FX = 0, FY = 1, XFX = 2, XFY = 3, YFX = 4, XF = 5, YF = 6;
    private Set<OpDef> ops;

    private PrologOperatorSet() {
        this.ops = new LinkedHashSet<OpDef>();
    }

    public static PrologOperatorSet createStandardSet() {
        final PrologOperatorSet set = new PrologOperatorSet();
        set.add(1200, PrologOperatorSet.XFX, ":-");
        set.add(1200, PrologOperatorSet.XFX, "-->");
        set.add(1200, PrologOperatorSet.FX, ":-");
        set.add(1200, PrologOperatorSet.FX, "?-");
        set.add(1150, PrologOperatorSet.FX, "mode");
        set.add(1150, PrologOperatorSet.FX, "public");
        set.add(1150, PrologOperatorSet.FX, "dynamic");
        set.add(1150, PrologOperatorSet.FX, "volatile");
        set.add(1150, PrologOperatorSet.FX, "discontiguous");
        set.add(1150, PrologOperatorSet.FX, "multifile");
        set.add(1150, PrologOperatorSet.FX, "block");
        set.add(1150, PrologOperatorSet.FX, "meta_predicate");
        set.add(1150, PrologOperatorSet.FX, "initialization");
        set.add(1100, PrologOperatorSet.XFY, ";");
        set.add(1050, PrologOperatorSet.XFY, "->");
        set.add(1000, PrologOperatorSet.XFY, ",");
        set.add(900, PrologOperatorSet.FY, "\\+");
        set.add(900, PrologOperatorSet.FY, "spy");
        set.add(900, PrologOperatorSet.FY, "nospy");
        set.add(700, PrologOperatorSet.XFX, "=");
        set.add(700, PrologOperatorSet.XFX, "\\=");
        set.add(700, PrologOperatorSet.XFX, "is");
        set.add(700, PrologOperatorSet.XFX, "=..");
        set.add(700, PrologOperatorSet.XFX, "==");
        set.add(700, PrologOperatorSet.XFX, "\\==");
        set.add(700, PrologOperatorSet.XFX, "@<");
        set.add(700, PrologOperatorSet.XFX, "@>");
        set.add(700, PrologOperatorSet.XFX, "@=<");
        set.add(700, PrologOperatorSet.XFX, "@>=");
        set.add(700, PrologOperatorSet.XFX, "=:=");
        set.add(700, PrologOperatorSet.XFX, "=\\=");
        set.add(700, PrologOperatorSet.XFX, "<");
        set.add(700, PrologOperatorSet.XFX, ">");
        set.add(700, PrologOperatorSet.XFX, "=<");
        set.add(700, PrologOperatorSet.XFX, ">=");
        set.add(550, PrologOperatorSet.XFY, ":");
        set.add(500, PrologOperatorSet.YFX, "+");
        set.add(500, PrologOperatorSet.YFX, "-");
        set.add(500, PrologOperatorSet.YFX, "#");
        set.add(500, PrologOperatorSet.YFX, "/\\");
        set.add(500, PrologOperatorSet.YFX, "xor");
        set.add(500, PrologOperatorSet.YFX, "\\/");
        set.add(400, PrologOperatorSet.YFX, "*");
        set.add(400, PrologOperatorSet.YFX, "/");
        set.add(400, PrologOperatorSet.YFX, "//");
        set.add(400, PrologOperatorSet.YFX, "mod");
        set.add(400, PrologOperatorSet.YFX, "rem");
        set.add(400, PrologOperatorSet.YFX, "<<");
        set.add(400, PrologOperatorSet.YFX, ">>");
        set.add(200, PrologOperatorSet.XFX, "**");
        set.add(200, PrologOperatorSet.XFY, "^");
        set.add(200, PrologOperatorSet.FY, "+");
        set.add(200, PrologOperatorSet.FY, "-");
        set.add(200, PrologOperatorSet.FY, "\\");
        return set;
    }

    public boolean isOperator(final String name) {
        return this.getOpNames().contains(name);
    }

    public boolean hasFixity(final String op, final int fix) {
        return this.isOperator(op) && this.ops.contains(new OpDef(0, fix, op));
    }

    public int[] getFixity(final String op) {
        if (this.isOperator(op)) {
            final ArrayList<Integer> fix = new ArrayList<Integer>();
            for (final OpDef def : this.ops) {
                if (def.matches(op)) {
                    fix.add(Integer.valueOf(def.fixity));
                }
            }
            final int[] res = new int[fix.size()];
            for (int i = 0; i < res.length; i++) {
                res[i] = fix.get(i).intValue();
            }
            return res;
        } else {
            return new int[0];
        }
    }

    public boolean hasPrecedence(final String op, final int prec) {
        final int[] precs = this.getPrecedence(op);
        for (final int i : precs) {
            if (i == prec) {
                return true;
            }
        }
        return false;
    }

    public int[] getPrecedence(final String op) {
        if (this.isOperator(op)) {
            final ArrayList<Integer> precs = new ArrayList<Integer>();
            for (final OpDef def : this.ops) {
                if (def.matches(op)) {
                    precs.add(Integer.valueOf(def.precedence));
                }
            }
            final int[] res = new int[precs.size()];
            for (int i = 0; i < res.length; i++) {
                res[i] = precs.get(i).intValue();
            }
            return res;
        } else {
            return new int[0];
        }
    }

    public int getPrecedence(final String op, final int fixity) {
        if (this.isOperator(op)) {
            for (final OpDef def : this.ops) {
                if (def.matches(op)) {
                    if (def.fixity == fixity) {
                        return def.precedence;
                    }
                }
            }
        }
        return -1;
    }

    public PrologOperatorSet getFixitySet(final int fixity) {
        final PrologOperatorSet forReturn = new PrologOperatorSet();
        for (final OpDef def : this.ops) {
            if (def.fixity == fixity) {
                forReturn.add(def);
            }
        }
        return forReturn;
    }

    /**
     * Creates a partition of this PrologOperatorSet according to the 7
     * different fixity types an operator may have.
     * @return An PrologOperatorSet array for the 7 different fixity types
     * an operator may have as a partition of this PrologOperatorSet.
     */
    public PrologOperatorSet[] getFixitySets() {
        final PrologOperatorSet[] forReturn = new PrologOperatorSet[7];
        for (int i = 0; i < forReturn.length; i++) {
            forReturn[i] = new PrologOperatorSet();
            for (final OpDef def : this.ops) {
                if (def.fixity == i) {
                    forReturn[i].add(def);
                }
            }
        }
        return forReturn;
    }

    public boolean isEmpty() {
        return this.ops.isEmpty();
    }

    public void add(final int precedence, final int fixity, final String op) {
        final OpDef def = new OpDef(precedence, fixity, op);
        this.add(def);
    }

    public void add(final OpDef def) {
        OpDef toDel = null;
        for (final OpDef op : this.ops) { // ops.contains(def) does not work - inconsistency?
            if (op.equals(def)) {
                toDel = op;
                break;
            }
        }
        if (toDel != null) {
            this.ops.remove(toDel);
        }
        if (def.precedence > 0) {
            this.ops.add(def);
        }
    }

    @Override
    public String toString() {
        String res = "Operators:\n";
        for (final OpDef def : this.ops) {
            res += def.toString() + "\n";
        }
        return res;
    }

    private Set<String> getOpNames() {
        final Set<String> names = new LinkedHashSet<String>();
        for (final OpDef def : this.ops) {
            names.add(def.name);
        }
        return names;
    }

    private class OpDef {
        private final String name;
        private final int precedence, fixity;

        private OpDef(final int p, final int f, final String op) {
            if (p < 0 || p > 1200 || f < 0 || f > 6 || op == null || op.equals("")) {
                throw new IllegalArgumentException("Wrong parameters!");
            }
            this.name = op;
            this.precedence = p;
            this.fixity = f;
        }

        public boolean matches(final String op) {
            return this.name.equals(op);
        }

        @Override
        public boolean equals(final Object o) {
            if (o instanceof OpDef) {
                return this.equals((OpDef) o);
            }
            return false;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + this.fixity;
            result = prime * result + ((this.name == null) ? 0 : this.name.hashCode());
            return result;
        }

        public boolean equals(final OpDef def) {
            if (def.name.equals(this.name)) {
                switch (def.fixity) {
                case FX:
                case FY:
                    return this.fixity == PrologOperatorSet.FX || this.fixity == PrologOperatorSet.FY;
                case XFX:
                case YFX:
                case XFY:
                case XF:
                case YF:
                    return this.fixity == PrologOperatorSet.XFX || this.fixity == PrologOperatorSet.YFX || this.fixity == PrologOperatorSet.XFY || this.fixity == PrologOperatorSet.XF
                        || this.fixity == PrologOperatorSet.YF;
                }
            }
            return false;
        }

        @Override
        public String toString() {
            String res = this.name + "(";
            switch (this.fixity) {
            case FX:
                res += "fx";
                break;
            case FY:
                res += "fy";
                break;
            case XFX:
                res += "xfx";
                break;
            case XFY:
                res += "xfy";
                break;
            case YFX:
                res += "yfx";
                break;
            case XF:
                res += "xf";
                break;
            case YF:
                res += "yf";
                break;
            default:
                throw new IllegalStateException("Unknown fixity!");
            }
            res += "," + this.precedence + ")";
            return res;
        }
    }

    /**
     * @return
     */
    public PrologOperatorSet copy() {
        final PrologOperatorSet res = new PrologOperatorSet();
        res.ops = this.ops;
        return res;
    }
}
