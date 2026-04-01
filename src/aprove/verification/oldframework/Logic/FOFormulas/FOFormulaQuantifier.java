package aprove.verification.oldframework.Logic.FOFormulas;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * Base class for FO quantifiers (FORALL, EXISTS)
 * @Author Andreas Kelle-Emden
 */
public class FOFormulaQuantifier extends FOFormula {
    protected FOFormula formula;
    protected List<TRSVariable> vars;

    // specials
    protected String skolemid = "";
    protected String qid = "";
    protected List<TRSTerm> pats;
    protected List<TRSTerm> nopats;
    protected boolean promote = false;
    protected List<TRSTerm> mpat;

    public static final int SPECIAL_SKOLEM  = 1;
    public static final int SPECIAL_QID     = 2;
    public static final int SPECIAL_PATS    = 3;
    public static final int SPECIAL_NOPATS  = 4;
    public static final int SPECIAL_PROMOTE = 5;
    public static final int SPECIAL_MPAT    = 6;


    public FOFormulaQuantifier (List<TRSVariable> vars, FOFormula formula) {
        this.vars = vars;
        this.formula = formula;
        this.pats = new ArrayList<TRSTerm>();
        this.mpat = new ArrayList<TRSTerm>();
        this.nopats = new ArrayList<TRSTerm>();
    }

    public void setPromote(boolean b) {
        this.promote = b;
    }

    public void setSkolemId (String s) {
        this.skolemid = s;
    }

    public void setSkolemId (int i) {
        this.skolemid = ""+i;
    }

    public void setSkolemId (Integer i) {
        this.skolemid = i.toString();
    }

    public void setQid (String s) {
        this.qid = s;
    }

    public void setQid (int i) {
        this.qid = ""+i;
    }

    public void setQid (Integer i) {
        this.qid = i.toString();
    }

    public void addPat (TRSTerm t) {
        this.pats.add(t);
    }

    public void addNoPat (TRSTerm t) {
        this.nopats.add(t);
    }

    public void addMPat (TRSTerm t) {
        this.mpat.add(t);
    }

    @Override
    public String toString() {
        String s = "(";
        for (TRSVariable v : this.vars) {
            s += " " + v.toString();
        }
        s += ") ";
        if (this.pats.size() > 0) {
            s += "(PATS";
            for (TRSTerm t : this.pats) {
                s += " " + t.toString();
            }
            s += ") ";
        }
        if (this.mpat.size() > 0) {
            s += "(PATS (MPAT";
            for (TRSTerm t : this.mpat) {
                s += " " + t.toString();
            }
            s += ")) ";
        }
        if (this.nopats.size() > 0) {
            s += "(NOPATS";
            for (TRSTerm t : this.nopats) {
                s += " " + t.toString();
            }
            s += ") ";
        }
        if (this.promote) {
            s += "(PATS PROMOTE) ";
        }
        if (!this.skolemid.equals("")) {
            s += "(SKOLEMID " + this.skolemid + ") ";
        }
        if (!this.qid.equals("")) {
            s += "(QID " + this.qid + ") ";
        }
        s += this.formula.toString();
        return s;
    }

}
