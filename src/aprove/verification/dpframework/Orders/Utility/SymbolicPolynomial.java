/*
 * Created on 31.03.2003
 *
 */
package aprove.verification.dpframework.Orders.Utility;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * @author thiemann
 * stores linear polyniomials as Mapping from Variables to Coefficients
 * + an additional integer for the constant
 */
public class SymbolicPolynomial implements HTML_Able {
    protected HashMap varMapping; // String -> Integer
    protected int constant;

    protected SymbolicPolynomial(int constant) {
        this.constant = constant;
        this.varMapping = new HashMap();
    }


    /**
     * Construct a new poly out of a multiterm as needed for ACRPOS.
     */
    public static SymbolicPolynomial createSymbolicPolynomial(FlattenedMultiterm t) {
        SymbolicPolynomial res = new SymbolicPolynomial(0);
        List<TRSTerm> args = FlattenedMultiterm.toTerm(t.getMultiArguments()).toList();
        Iterator i = args.iterator();

        while(i.hasNext()) {
        TRSTerm tt = (TRSTerm)i.next();
        if(tt.isVariable()) {
            String varname = ((TRSVariable)tt).getName();
            Object old = res.varMapping.get(varname);
            int newint = 1;
            if(old!=null) {
            newint += ((Integer)old).intValue();
            }
            res.varMapping.put(varname, Integer.valueOf(newint));
        }
        else {
            res.constant++;
        }
        }

        return res;
    }

    /**
     * Construct a new poly out of a multiterm as needed for ACQRPOS.
     */
    public static SymbolicPolynomial createSymbolicPolynomial(FlattenedQuasiMultiterm t) {
        SymbolicPolynomial res = new SymbolicPolynomial(0);
        List<TRSTerm> args = FlattenedQuasiMultiterm.toTerm(t.getMultiArguments()).toList();
        Iterator i = args.iterator();

        while(i.hasNext()) {
        TRSTerm tt = (TRSTerm)i.next();
        if(tt.isVariable()) {
            String varname = ((TRSVariable)tt).getName();
            Object old = res.varMapping.get(varname);
            int newint = 1;
            if(old!=null) {
            newint += ((Integer)old).intValue();
            }
            res.varMapping.put(varname, Integer.valueOf(newint));
        }
        else {
            res.constant++;
        }
        }

        return res;
    }

    /**
     * Compares as needed for ACRPOS and ACQRPOS, i.e. only in positive integers
     * excluding 0.
     */
    public OrderRelation compareToPositive(SymbolicPolynomial p) {
        if(p==null) {
        return null;
        }

        int thismin = this.minInPositives();
        int pmin = p.minInPositives();
        if(thismin < pmin) {
        return null;
        }

        Iterator pVars = p.varMapping.entrySet().iterator();
        while(pVars.hasNext()) {
            Map.Entry p_vn = (Map.Entry) pVars.next();
        String pVar = (String) p_vn.getKey();
        Integer thisN = (Integer) this.varMapping.get(pVar);
        if(thisN == null) {
            return null;
        }
        if(thisN.intValue() < ((Integer) p_vn.getValue()).intValue()) {
            return null;
        }
        }

        if(thismin == pmin) {
        return OrderRelation.GE;
        }
        return OrderRelation.GR;
    }

        private int minInPositives() {
        int res = this.constant;
        Iterator thisVars = this.varMapping.entrySet().iterator();
        while(thisVars.hasNext()) {
            Map.Entry p_vn = (Map.Entry) thisVars.next();
        String pVar = (String) p_vn.getKey();
        Integer thisN = (Integer) this.varMapping.get(pVar);
        if(thisN != null) {
            res += thisN.intValue();
        }
        }
        return res;
    }


    /**
     * Adds the two polys into a new poly
     * @param p1
     * @param p2
     * @return SymbolicPolynomial
     */
    public static SymbolicPolynomial add(SymbolicPolynomial p1, SymbolicPolynomial p2) {
        if (p1 == null || p2 == null) {
            return null;
        }
        SymbolicPolynomial p = new SymbolicPolynomial(p1.constant+p2.constant);
        p.varMapping = new HashMap(p2.varMapping);
        Iterator p1vars = p1.varMapping.entrySet().iterator();
        while (p1vars.hasNext()) {
            Map.Entry entry = (Map.Entry) p1vars.next();
            Object var = entry.getKey();
            int p1Int = ((Integer) entry.getValue()).intValue();
            Integer maybep2Int = (Integer) p.varMapping.get(entry.getKey());
            if (maybep2Int != null) {
                p1Int = p1Int + maybep2Int.intValue();
            }
            p.varMapping.put(var,Integer.valueOf(p1Int));
        }
        return p;
    }

    /**
     * compares this poly with another one,
     * results are taken from Constraint
     * @param p
     * @return int
     */
    public OrderRelation compareTo(SymbolicPolynomial p) {
        if (p==null) {
            return null;
        }
        if (this.constant < p.constant) {
            return null;
        }
        Iterator pVars = p.varMapping.entrySet().iterator();
        while (pVars.hasNext()) {
            Map.Entry p_vn = (Map.Entry) pVars.next();
            String pVar = (String) p_vn.getKey();
            Integer thisN = (Integer) this.varMapping.get(pVar);
            if (thisN == null) {
                return null;
            }
            if (thisN.intValue() < ((Integer) p_vn.getValue()).intValue()) {
                return null;
            }
        }
        if (this.constant == p.constant) {
            return OrderRelation.GE;
        }
        return OrderRelation.GR;
    }

    public Polynomial transformToPolynomial() {
        Iterator i = this.varMapping.entrySet().iterator();
        Polynomial p = Polynomial.ZERO;
        while (i.hasNext()) {
            Map.Entry entry = (Map.Entry) i.next();
            String var = (String) entry.getKey();
            Polynomial varP = Polynomial.createVariable(var);
            int coeff = ((Integer) entry.getValue()).intValue();
            Polynomial coeffP = Polynomial.createConstant(coeff);
            p = p.plus(coeffP.times(varP));
        }
        Polynomial constP = Polynomial.createConstant(this.constant);
        p = p.plus(constP);
        return p;
    }

    @Override
    public String toHTML() {
        return this.transformToPolynomial().toHTML();
    }
}
