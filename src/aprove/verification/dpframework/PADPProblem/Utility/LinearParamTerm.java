package aprove.verification.dpframework.PADPProblem.Utility;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

public class LinearParamTerm implements Exportable {

    private LinkedHashMap<TRSVariable, SimplePolynomial> theMap;

    private SimplePolynomial constant;

    /**
     *
     */
    private LinearParamTerm() {
        this.theMap = new LinkedHashMap<TRSVariable, SimplePolynomial>();
        this.constant = SimplePolynomial.create(0);
    }

    public LinearParamTerm(TRSVariable x) {
        this.theMap = new LinkedHashMap<TRSVariable, SimplePolynomial>();
        this.constant = SimplePolynomial.create(0);
        this.theMap.put(x, SimplePolynomial.ONE);
    }

    public LinearParamTerm(String a) {
        this.theMap = new LinkedHashMap<TRSVariable, SimplePolynomial>();
        this.constant = SimplePolynomial.create(a);
    }

    public LinearParamTerm(int i) {
        this.theMap = new LinkedHashMap<TRSVariable, SimplePolynomial>();
        this.constant = SimplePolynomial.create(i);
    }

    public LinearParamTerm(Map<TRSVariable, SimplePolynomial> theMap, SimplePolynomial constant) {
        this.theMap = new LinkedHashMap<TRSVariable, SimplePolynomial>(theMap);
        this.constant = constant;
    }

    private SimplePolynomial get_map(TRSVariable v) {
        SimplePolynomial res = this.theMap.get(v);
        if (res == null) {
            return SimplePolynomial.create(0);
        } else {
            return res;
        }
    }

    /**
     * Returns the variables.
     */
    public Set<TRSVariable> getVariables() {
        return new LinkedHashSet<TRSVariable>(this.theMap.keySet());
    }

    public SimplePolynomial getCoefficient(TRSVariable v) {
        return this.theMap.get(v);
    }

    public SimplePolynomial getConstant() {
        return this.constant;
    }

    /**
     * Multiplies by a SimplePolynomial and returns a new LinearParamTerm.
     */
    public LinearParamTerm mult(SimplePolynomial sp) {
        LinearParamTerm res = new LinearParamTerm();
        if (!sp.equals(SimplePolynomial.ZERO)) {
            for (TRSVariable v : this.theMap.keySet()) {
                res.theMap.put(v, this.theMap.get(v).times(sp));
            }
            res.constant = this.constant.times(sp);
        }
        return res;
    }

    /**
     *  Removes a variable.
     */
    public void removeVariable(TRSVariable v) {
        this.theMap.remove(v);
    }

    /**
     * Adds a LinearParamTerm and returns a new LinearParamTerm.
     */
    public LinearParamTerm add(LinearParamTerm lpt) {
        LinearParamTerm res = new LinearParamTerm();
        Set<TRSVariable> allVars = new LinkedHashSet<TRSVariable>(this.theMap.keySet());
        allVars.addAll(lpt.theMap.keySet());
        for (TRSVariable v : allVars) {
            SimplePolynomial sum = this.get_map(v).plus(lpt.get_map(v));
            if (!sum.equals(SimplePolynomial.ZERO)) {
                res.theMap.put(v, sum);
            }
        }
        res.constant = this.constant.plus(lpt.constant);
        return res;
    }

    /**
     * Subtracts a LinearParamTerm and returns a new LinearParamTerm.
     */
    public LinearParamTerm minus(LinearParamTerm lpt) {
        return this.add(lpt.mult(SimplePolynomial.MINUS_ONE));
    }

    /**
     * Instantiates a variable by a LinearParamTerm and returns a new LinearParamTerm.
     */
    public LinearParamTerm instantiate(TRSVariable v, LinearParamTerm lpt) {
        LinearParamTerm res = new LinearParamTerm();
        res.constant = this.constant;
        SimplePolynomial vpoly = null;
        for (TRSVariable w : this.theMap.keySet()) {
            if (!w.equals(v)) {
                res.theMap.put(w, this.theMap.get(w));
            } else {
                vpoly = this.theMap.get(w);
            }
        }
        if (vpoly != null) {
            res = res.add(lpt.mult(vpoly));
        }
        return res;
    }

    public LinearParamTerm substituteVariables(Map<TRSVariable, LinearParamTerm> subst) {
        LinearParamTerm res = new LinearParamTerm();
        res.theMap = new LinkedHashMap<TRSVariable, SimplePolynomial>(this.theMap);
        res.constant = this.constant;
        for (TRSVariable v : subst.keySet()) {
            LinearParamTerm lpt = subst.get(v);
            res = res.instantiate(v, lpt);
        }
        return res;
    }

    /**
     * Instantiates a variable by a LinearTerm and returns a new LinearParamTerm.
     */
    public LinearParamTerm instantiate(TRSVariable v, LinearTerm lt) {
        LinearParamTerm lpt = lt.toLinearParamTerm();
        return this.instantiate(v, lpt);
    }

    /**
     * Evaluates for a given parameter assignment.
     */
    public LinearTerm evaluate(Map<String, BigInteger> assignment) {
        Integer constant = this.get(this.constant.specialize(assignment));
        Map<TRSVariable, Integer> theMap = new LinkedHashMap<TRSVariable, Integer>();
        for (TRSVariable v : this.theMap.keySet()) {
            theMap.put(v, this.get(this.theMap.get(v).specialize(assignment)));
        }
        return new LinearTerm(theMap, constant);
    }

    private Integer get(SimplePolynomial sp) {
        if (!sp.isConstant()) {
            throw new RuntimeException("No binding for some parameter in LinearParamTerm.evaluate");
        }
        return Integer.valueOf(sp.getNumericalAddend().intValue());
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        List<String> monos = new Vector<String>();
        for (TRSVariable v : this.theMap.keySet()) {
            String s = this.getMonoString(v, this.theMap.get(v), eu);
            if (!s.equals("")) {
                monos.add(s);
            }
        }
        res.append(this.getMonoString(monos));
        if (monos.size() == 0) {
            res.append(this.constant);
        } else if (!this.constant.equals(SimplePolynomial.ZERO)) {
            res.append(" + " + this.SPString(this.constant, eu));
        }
        return res.toString();
    }

    private String SPString(SimplePolynomial sp, Export_Util eu) {
        if (sp.isConstant() || sp.isIndefinite()) {
            return sp.export(eu);
        } else {
            return "(" + sp.export(eu) + ")";
        }
    }

    private String getMonoString(TRSVariable v, SimplePolynomial sp, Export_Util eu) {
       
        if (sp.equals(SimplePolynomial.ZERO)) {
            return "";
        } else if (sp.equals(SimplePolynomial.ONE)) {
            String vname = v.getName();
            String[] split = vname.split("_", 2);
            StringBuilder varBuf = new StringBuilder(split[0]);
            varBuf.append(eu.sub(split[1]));
            return varBuf.toString();
        } else {
            String vname = v.getName();
            String[] split = vname.split("_", 2);
            StringBuilder varBuf = new StringBuilder(this.SPString(sp, eu));
            varBuf.append("*");
            varBuf.append(split[0]);
            varBuf.append(eu.sub(split[1]));
            return varBuf.toString();
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

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public LinearParamTerm substituteParameters(Map<String, BigInteger> subst) {
        LinearParamTerm res = new LinearParamTerm();
        res.theMap = new LinkedHashMap<TRSVariable, SimplePolynomial>();
        res.constant = this.constant.specialize(subst);
        for (TRSVariable v : this.theMap.keySet()) {
            res.theMap.put(v, this.theMap.get(v).specialize(subst));
        }
        return res;
    }

}
