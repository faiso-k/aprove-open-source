package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;


/**
 * A PAConstraint is an atom s > t, s >= t or s = t.
 *
 * @author Stephan Falke
 * @version $Id$
 */
public class PAConstraint implements Immutable, Exportable, HasVariables {

    public final static Relation GTR = Relation.GTR;
    public final static Relation GTREQ = Relation.GTREQ;
    public final static Relation EQ = Relation.EQ;

    public enum Relation {
        GTR, GTREQ, EQ;
    }

    protected TRSTerm l;
    protected TRSTerm r;
    protected Relation type;

    private PAConstraint(TRSTerm l, TRSTerm r, Relation type) {
        this.l = l;
        this.r = r;
        this.type = type;
    }

    public static PAConstraint create(TRSTerm l, TRSTerm r, Relation type) {
        return new PAConstraint(l, r, type);
    }

    public TRSTerm getLeft() {
        return this.l;
    }

    public TRSTerm getRight() {
        return this.r;
    }

    public Relation getType() {
        return this.type;
    }

    /**
     * returns the set of variables occurring in this PAConstraint
     */
    @Override
    public Set<TRSVariable> getVariables() {
        Set<TRSVariable> res = this.l.getVariables();
        res.addAll(this.r.getVariables());
        return res;
    }

    @Override
    public String export(Export_Util eu) {
        return this.l.export(eu) + " " + this.getRel(eu) + " " + this.r.export(eu);
    }

    private String getRel(Export_Util eu) {
        if (this.type == PAConstraint.GTR) {
            return eu.gtSign();
        } else if (this.type == PAConstraint.GTREQ) {
            return eu.geSign();
        } else {
            return eu.eqSign();
        }
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public int hashCode() {
        return this.toString().hashCode();
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        if (other == null) {
            return false;
        }
        if (other instanceof PAConstraint) {
            PAConstraint cond = (PAConstraint) other;
            return this.l.equals(cond.l) && this.r.equals(cond.r) && this.type == cond.type;
        }
        return false;
    }

    /**
     * returns conjunction of PAConstraints as a benchmark in SMTLIB format
     */
    public static String toSMTLIB(Set<PAConstraint> c) {
        List<String> res = new Vector<String>();
        Set<TRSVariable> varss = new LinkedHashSet<TRSVariable>();
        for (PAConstraint cc : c) {
            res.add(cc.toSMTLIB());
            varss.addAll(cc.getVariables());
        }
        return PAConstraint.buildBenchmark(res, varss);
    }

    private static String buildBenchmark(List<String> atomss, Set<TRSVariable> varss) {
        StringBuilder s = new StringBuilder();
        s.append("(benchmark dummbrot\n");
        s.append(":logic QF_LIA\n");

        if (!varss.isEmpty()) {
            s.append(":extrafuns (");
            for (TRSVariable v : varss) {
                s.append(" (" + v.getName());
                s.append(" Int)");
            }
            s.append(")\n");
        }

        StringBuilder ss = new StringBuilder();
        PAConstraint.buildConjunction(ss, atomss);

        s.append(":formula ");
        s.append(ss);

        s.append("\n)\n\n");

        return s.toString();
    }

    private static void buildConjunction(StringBuilder s, List<String> atomss) {
        if (atomss.isEmpty()) {
            s.append("(true)");
        } else {
            s.append("(and");
            for (String sf : atomss) {
                s.append(" ");
                s.append(sf);
            }
            s.append(" )");
        }
    }

    /**
     * returns a PAConstraint as an atom in SMTLIB format
     */
    public String toSMTLIB() {
        String ls = this.term_toSMTLIB(this.l);
        String rs = this.term_toSMTLIB(this.r);
        switch (this.type) {
        case GTR:
            return "(> (" + ls + ") (" + rs + "))";
        case GTREQ:
            return "(>= (" + ls + ") (" + rs + "))";
        default:
            return "(= (" + ls + ") (" + rs + "))";
        }
    }

    private String term_toSMTLIB(TRSTerm t) {
        Map<TRSVariable, Integer> map = new LinkedHashMap<TRSVariable, Integer>();
        map.put(new TRSVariable("@@@"), Integer.valueOf(0));
        this.create_map(t, false, map);
        return this.toSMTLIB_aux(map);
    }

    private String toSMTLIB_aux(Map<TRSVariable, Integer> map) {
        StringBuilder res = new StringBuilder("(+ ");
        for (TRSVariable v : map.keySet()) {
            res.append(this.toSMTLIB_aux2(v, map.get(v)));
        }
        res.append(" )");
        return res.toString();
    }

    private String toSMTLIB_aux2(TRSVariable v, Integer i) {
        if (v.getName().equals("@@@")) {
            return "(" + this.toSMTLIB_aux3(i) + ")";
        } else {
            return "(* " + this.toSMTLIB_aux3(i) + " " + v.getName() + " )";
        }
    }

    private String toSMTLIB_aux3(Integer i) {
        int it = i.intValue();
        if (it < 0) {
            return "(- " + (Integer.valueOf(Math.abs(it))).toString() + ")";
        } else {
            return i.toString();
        }
    }

    private void create_map(TRSTerm t, boolean isneg, Map<TRSVariable, Integer> map) {
        if (t instanceof TRSVariable) {
            Integer sofar = this.get_map((TRSVariable) t, map);
            map.put((TRSVariable) t, Integer.valueOf(sofar.intValue() + this.get_coeff(isneg)));
        } else {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            String f = ft.getRootSymbol().getName();
            if (f.equals("0")) {
                return;
            } else if (f.equals("1")) {
                TRSVariable dummy = new TRSVariable("@@@");
                Integer sofar = this.get_map(dummy, map);
                map.put(dummy, Integer.valueOf(sofar.intValue() + this.get_coeff(isneg)));
            } else if (f.equals("+")) {
                this.create_map(ft.getArgument(0), isneg, map);
                this.create_map(ft.getArgument(1), isneg, map);
            } else if (f.equals("-")) {
                this.create_map(ft.getArgument(0), !isneg, map);
            } else {
                throw new RuntimeException("internal error in PAConstraint.create_map: Could not map Term " + t);
            }
        }
    }

    private Integer get_map(TRSVariable v, Map<TRSVariable, Integer> map) {
        Integer res = map.get(v);
        if (res == null) {
            return Integer.valueOf(0);
        } else {
            return res;
        }
    }

    private int get_coeff(boolean isneg) {
        if (isneg) {
            return -1;
        } else {
            return 1;
        }
    }

}
