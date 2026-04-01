package aprove.verification.dpframework.PADPProblem.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

public class LinearTerm {

    private LinkedHashMap<TRSVariable, Integer> theMap;

    private Integer constant;

    /**
     * Construct a LinearTerm from a plain term.
     */
    public LinearTerm(TRSTerm t) {
        this.theMap = new LinkedHashMap<TRSVariable, Integer>();
        this.constant = Integer.valueOf(0);
        if (t != null) {
            this.create_map(t, false);
            this.filter_map();
        }
    }

    /**
     * Construct a LinearTerm from a map and an Integer.
     */
    public LinearTerm(Map<TRSVariable, Integer> theMap, Integer constant) {
        this.theMap = new LinkedHashMap<TRSVariable, Integer>(theMap);
        this.constant = Integer.valueOf(constant.intValue());
    }

    private void filter_map() {
        Map<TRSVariable, Integer> tmp = new LinkedHashMap<TRSVariable, Integer>(this.theMap);
        this.theMap.clear();
        for (TRSVariable v : tmp.keySet()) {
            Integer i = tmp.get(v);
            if (i.intValue() != 0) {
                this.theMap.put(v, i);
            }
        }
    }

    private void create_map(TRSTerm t, boolean isneg) {
        if (t instanceof TRSVariable) {
            Integer sofar = this.get_map((TRSVariable) t);
            this.theMap.put((TRSVariable) t, Integer.valueOf(sofar.intValue() + this.get_coeff(isneg)));
        } else {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            String f = ft.getRootSymbol().getName();
            if (f.equals("0")) {
                return;
            } else if (f.equals("1")) {
                this.constant = Integer.valueOf(this.constant.intValue() + this.get_coeff(isneg));
            } else if (f.equals("+")) {
                this.create_map(ft.getArgument(0), isneg);
                this.create_map(ft.getArgument(1), isneg);
            } else if (f.equals("-")) {
                this.create_map(ft.getArgument(0), !isneg);
            } else {
                throw new RuntimeException("internal error in LinearTerm.create_map");
            }
        }
    }

    private Integer get_map(TRSVariable v) {
        Integer res = this.theMap.get(v);
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

    /**
     * Returns the variables.
     */
    public Set<TRSVariable> getVariables() {
        return new LinkedHashSet<TRSVariable>(this.theMap.keySet());
    }

    public Integer getConstant() {
        return this.constant;
    }

    public Integer getCoefficient(TRSVariable v) {
        return this.theMap.get(v);
    }

    public LinearParamTerm toLinearParamTerm() {
        SimplePolynomial constant = SimplePolynomial.create(this.constant.intValue());
        Map<TRSVariable, SimplePolynomial> theMap = new LinkedHashMap<TRSVariable, SimplePolynomial>();
        for (TRSVariable v : this.theMap.keySet()) {
            theMap.put(v, SimplePolynomial.create(this.theMap.get(v).intValue()));
        }
        return new LinearParamTerm(theMap, constant);
    }

    /**
     * Multiplies by a constant and returns a new LinearTerm.
     */
    public LinearTerm mult(Integer i) {
        LinearTerm res = new LinearTerm(null);
        int d = i.intValue();
        if (d != 0) {
            for (TRSVariable v : this.theMap.keySet()) {
                res.theMap.put(v, Integer.valueOf(this.theMap.get(v).intValue() * d));
            }
            res.constant = Integer.valueOf(this.constant.intValue() * d);
        }
        return res;
    }

    /**
     * Adds a LinearTerm and returns a new LinearTerm.
     */
    public LinearTerm add(LinearTerm lt) {
        LinearTerm res = new LinearTerm(null);
        Set<TRSVariable> allVars = new LinkedHashSet<TRSVariable>(this.theMap.keySet());
        allVars.addAll(lt.theMap.keySet());
        for (TRSVariable v : allVars) {
            int newval = this.get_map(v).intValue() + lt.get_map(v).intValue();
            if (newval != 0) {
                res.theMap.put(v, Integer.valueOf(newval));
            }
        }
        res.constant = Integer.valueOf(this.constant.intValue() + lt.constant.intValue());
        return res;
    }

    /**
     * Subtracts a LinearTerm and returns a new LinearTerm.
     */
    public LinearTerm minus(LinearTerm lt) {
        return this.add(lt.mult(Integer.valueOf(-1)));
    }

    /**
     * Instantiates a variable by a LinearTerm and returns a new LinearTerm.
     */
    public LinearTerm instantiate(TRSVariable v, LinearTerm lt) {
        LinearTerm res = new LinearTerm(null);
        res.constant = Integer.valueOf(this.constant.intValue());
        Integer vconst = null;
        for (TRSVariable w : this.theMap.keySet()) {
            if (!w.equals(v)) {
                res.theMap.put(w, this.theMap.get(w));
            } else {
                vconst = this.theMap.get(w);
            }
        }
        if (vconst != null) {
            res = res.add(lt.mult(vconst));
        }
        return res;
    }

    /**
     * Evaluates for a given variable assignment.
     */
    public Integer evaluate(Map<TRSVariable, Integer> assignment) {
        int res = this.constant.intValue();
        for (TRSVariable v : this.theMap.keySet()) {
            Integer val = assignment.get(v);
            if (val == null) {
                throw new RuntimeException("No binding for variable " + v + " in LinearTerm.evaluate");
            }
            res = res + (val.intValue() * this.theMap.get(v).intValue());
        }
        return Integer.valueOf(res);
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        List<String> monos = new Vector<String>();
        for (TRSVariable v : this.theMap.keySet()) {
            String s = this.getMonoString(v, this.theMap.get(v));
            if (!s.equals("")) {
                monos.add(s);
            }
        }
        res.append(this.getMonoString(monos));
        if (monos.size() == 0) {
            res.append(this.constant);
        } else if (this.constant.intValue() != 0) {
            res.append(" + " + this.constant);
        }
        return res.toString();
    }

    private String getMonoString(TRSVariable v, Integer i) {
        int d = i.intValue();
        if (d == 0) {
            return "";
        } else {
            return i + "*" + v;
        }
    }

    private String getMonoString(List<String> monos) {
        boolean notfirst = false;
        StringBuilder res = new StringBuilder();
        for (String s : monos) {
            if (notfirst) {
                res.append(" + " + s);
            } else {
                res.append(s);
                notfirst = true;
            }
        }
        return res.toString();
    }

    public boolean isUnivariate() {
        return this.getVariables().size() == 1;
    }

    public LinearTerm strengthen() {
        if (!this.isUnivariate()) {
            return this;
        }

        Map<TRSVariable, Integer> newMap = new LinkedHashMap<TRSVariable, Integer>();
        int constant = this.constant.intValue();
        int coeff = 0;
        for (TRSVariable v : this.theMap.keySet()) {
            newMap.put(v, Integer.valueOf(Integer.signum(this.theMap.get(v).intValue())));
            coeff = this.theMap.get(v);
        }
        float constantf = (float) constant;
        float coefff = (float) coeff;
        constant = (int) Math.floor(constantf / Math.abs(coefff));

        return new LinearTerm(newMap, Integer.valueOf(constant));
    }

}
