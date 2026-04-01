package aprove.verification.dpframework.PADPProblem.Utility;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

public class MatrixParamTerm implements Exportable {

    private LinkedHashMap<TRSVariable, SimpleMatrix> theMap;

    private SimpleMatrix constant;

    private int dim;

    /**
     *
     */
    private MatrixParamTerm(int dim) {
        this.dim = dim;
        this.theMap = new LinkedHashMap<TRSVariable, SimpleMatrix>();
        this.constant = SimpleMatrix.create(1, dim, 0);
    }

    /**
     * The constant is filled with value, everything else is zero.
     */
    public MatrixParamTerm(int dim, int value) {
        this.dim = dim;
        this.theMap = new LinkedHashMap<TRSVariable, SimpleMatrix>();
        this.constant = SimpleMatrix.create(1, dim, value);
    }

    public MatrixParamTerm(int dim, TRSVariable x) {
        this.dim = dim;
        this.theMap = new LinkedHashMap<TRSVariable, SimpleMatrix>();
        this.constant = SimpleMatrix.create(1, dim, 0);
        this.theMap.put(x, SimpleMatrix.createUnit(dim));
    }

    /**
     * The constant is filled with coeff, everything else is zero.
     */
    public MatrixParamTerm(int dim, List<String> coeff) {
        this.dim = dim;
        this.theMap = new LinkedHashMap<TRSVariable, SimpleMatrix>();
        this.constant = SimpleMatrix.create(coeff);
    }

    public MatrixParamTerm(int dim, Map<TRSVariable, SimpleMatrix> theMap, SimpleMatrix constant) {
        this.dim = dim;
        this.theMap = new LinkedHashMap<TRSVariable, SimpleMatrix>(theMap);
        this.constant = constant;
    }

    private SimpleMatrix get_map(TRSVariable v) {
        SimpleMatrix res = this.theMap.get(v);
        if (res == null) {
            return SimpleMatrix.create(this.dim, this.dim, 0);
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

    public SimpleMatrix getCoefficient(TRSVariable v) {
        return this.theMap.get(v);
    }

    public SimpleMatrix getConstant() {
        return this.constant;
    }

    /**
     * Multiplies by a SimpleMatrix from the left and returns a new MatrixParamTerm.
     */
    public MatrixParamTerm mult(SimpleMatrix sm) {
        MatrixParamTerm res = new MatrixParamTerm(this.dim);
        if (!sm.equals(SimpleMatrix.create(sm.dimX(), sm.dimY(), 0))) {
            for (TRSVariable v : this.theMap.keySet()) {
                res.theMap.put(v, sm.times(this.theMap.get(v)));
            }
            res.constant = sm.times(this.constant);
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
     * Adds a MatrixParamTerm and returns a new MatrixParamTerm.
     */
    public MatrixParamTerm add(MatrixParamTerm mpt) {
        if (this.dim != mpt.dim) {
            throw new RuntimeException("Incompatible sizes in MatrixParamTerm.add");
        }
        MatrixParamTerm res = new MatrixParamTerm(this.dim);
        Set<TRSVariable> allVars = new LinkedHashSet<TRSVariable>(this.theMap.keySet());
        allVars.addAll(mpt.theMap.keySet());
        for (TRSVariable v : allVars) {
            SimpleMatrix sum = this.get_map(v).plus(mpt.get_map(v));
            if (!sum.equals(SimpleMatrix.create(sum.dimX(), sum.dimY(), 0))) {
                res.theMap.put(v, sum);
            }
        }
        res.constant = this.constant.plus(mpt.constant);
        return res;
    }

    /**
     * Subtracts a MatrixParamTerm and returns a new MatrixParamTerm.
     */
    public MatrixParamTerm minus(MatrixParamTerm mpt) {
        return this.add(mpt.negate());
    }

    public MatrixParamTerm negate() {
        MatrixParamTerm res = new MatrixParamTerm(this.dim);
        res.constant = this.constant.negate();
        for (TRSVariable v : this.theMap.keySet()) {
            res.theMap.put(v, this.theMap.get(v).negate());
        }
        return res;
    }

    /**
     * Instantiates a variable by a MatrixParamTerm and returns a new MatrixParamTerm.
     */
    public MatrixParamTerm instantiate(TRSVariable v, MatrixParamTerm mpt) {
        if (this.dim != mpt.dim) {
            throw new RuntimeException("Incompatible sizes in MatrixParamTerm.instantiate");
        }
        MatrixParamTerm res = new MatrixParamTerm(this.dim);
        res.constant = this.constant;
        SimpleMatrix vmatrix = null;
        for (TRSVariable w : this.theMap.keySet()) {
            if (!w.equals(v)) {
                res.theMap.put(w, this.theMap.get(w));
            } else {
                vmatrix = this.theMap.get(w);
            }
        }
        if (vmatrix != null) {
            res = res.add(mpt.mult(vmatrix));
        }
        return res;
    }

    /**
     * Instantiates a variable by a LinearTerm (suitably lifted) and returns a new MatrixParamTerm.
     */
    public MatrixParamTerm instantiate(TRSVariable v, LinearTerm lt) {
        MatrixParamTerm mpt = this.getMatrixParamTerm(lt);
        return this.instantiate(v, mpt);
    }

    private MatrixParamTerm getMatrixParamTerm(LinearTerm lt) {
        SimpleMatrix constant = SimpleMatrix.create(1, this.dim, lt.getConstant().intValue());
        Map<TRSVariable, SimpleMatrix> theMap = new LinkedHashMap<TRSVariable, SimpleMatrix>();
        for (TRSVariable v : lt.getVariables()) {
            theMap.put(v, SimpleMatrix.createDiagonal(this.dim, lt.getCoefficient(v).intValue()));
        }
        return new MatrixParamTerm(this.dim, theMap, constant);
    }

    public MatrixParamTerm substituteVariables(Map<TRSVariable, MatrixParamTerm> subst) {
        MatrixParamTerm res = new MatrixParamTerm(this.dim);
        res.theMap = new LinkedHashMap<TRSVariable, SimpleMatrix>(this.theMap);
        res.constant = this.constant;
        for (TRSVariable v : subst.keySet()) {
            MatrixParamTerm mpt = subst.get(v);
            res = res.instantiate(v, mpt);
        }
        return res;
    }

    /**
     * Evaluates for a given parameter assignment.
     */
    public MatrixParamTerm evaluate(Map<String, BigInteger> assignment) {
        MatrixParamTerm res = new MatrixParamTerm(this.dim);
        res.constant = this.constant.specialize(assignment);
        for (TRSVariable v : this.theMap.keySet()) {
            res.theMap.put(v, this.theMap.get(v).specialize(assignment));
        }
        return res;
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
        } else if (!this.constant.equals(SimpleMatrix.create(1, this.dim, 0))) {
            res.append(" + " + this.constant.export(eu));
        }
        return res.toString();
    }

    private String getMonoString(TRSVariable v, SimpleMatrix sm, Export_Util eu) {
        if (sm.equals(SimpleMatrix.create(this.dim, this.dim, 0))) {
            return "";
        } else {
            String vname = v.getName();
            String[] split = vname.split("_", 2);
            StringBuilder varBuf = new StringBuilder(sm.export(eu));
            varBuf.append("*");
            varBuf.append(split[0]);
            if (split.length > 1) {
                varBuf.append(eu.sub(split[1]));
            }
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

    public MatrixParamTerm substituteParameters(Map<String, BigInteger> subst) {
        MatrixParamTerm res = new MatrixParamTerm(this.dim);
        res.constant = this.constant.specialize(subst);
        for (TRSVariable v : this.theMap.keySet()) {
            res.theMap.put(v, this.theMap.get(v).specialize(subst));
        }
        return res;
    }

}
