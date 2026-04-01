package aprove.verification.dpframework.PADPProblem.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Applies magic to obtain Diophantine constraints that ensure that a MatrixParamTerm satisfies a ConstraintType.
 *
 * @author Stephan Falke
 * @version $Id$
 */

public class MatrixDioCreator {

    private int counter = 0;
    private boolean noIntDependence;
    private int dim;

    public MatrixDioCreator(boolean noIntDependence, int dim) {
        this.noIntDependence = noIntDependence;
        this.dim = dim;
    }

    /* first arg is <PAConstraints, mpt> */
    /* result is <dio const for satisfying ct, null> if ct <> GT or autostrict = false
     *           <dio const for satisfying >=, additional dio const for satisfying >> if ct = GE and autostrict = true
     *                                                                                boundedness is not computed!
     */
    public Pair<Set<Diophantine>, Set<Diophantine>> getDio(Pair<Set<LinearTerm>, MatrixParamTerm> inp, ConstraintType ct, boolean autostrict, Map<TRSVariable, String> varSorts, boolean expandBounded) {
        if (!this.hasIntVars(inp.y, varSorts)) {
            // easy case: no variables of sort int
            return this.getDio(inp.y, ct, autostrict);
        }

        // hard case
        Set<Diophantine> res1 = new LinkedHashSet<Diophantine>();
        Set<Diophantine> res2 = null;
        Pair<Set<LinearTerm>, MatrixParamTerm> rp = this.doTransformation(inp.x, inp.y, expandBounded);
        MatrixParamTerm mpt = rp.y;

        SimpleMatrix constant = mpt.getConstant();
        for (TRSVariable v : mpt.getVariables()) {
            SimpleMatrix sm = mpt.getCoefficient(v);
            if (v.getName().startsWith("!!_") || varSorts.get(v).equals("int")) {
                if (ct.equals(ConstraintType.EQ)) {
                    res1.addAll(this.getDio(sm, ConstraintType.EQ));
                } else {
                    // variables of sort int may be instantiated by integers
                    Pair<Integer, Integer> boundCond = this.getBound(v, rp.x);
                    if (boundCond == null) {
                        // no bound known
                        res1.addAll(this.getDio(sm, ConstraintType.EQ));
                    } else {
                        int factor = boundCond.x.intValue();
                        int bound = boundCond.y.intValue();
                        if (factor >= 0) {
                            res1.addAll(this.getDio(sm, ConstraintType.GE));
                        } else {
                            res1.addAll(this.getDio(sm.negate(), ConstraintType.GE));
                        }
                        constant = constant.plus(sm.times(SimpleMatrix.create(1, this.dim, -factor * bound)));
                    }
                }
            } else {
                // variable of sort univ which is instantiated by a natural number if this.noIntDependence is true
                if (ct.equals(ConstraintType.EQ)) {
                    res1.addAll(this.getDio(sm, ConstraintType.EQ));
                } else {
                    if (this.noIntDependence) {
                        res1.addAll(this.getDio(sm, ConstraintType.GE));
                    } else {
                        res1.addAll(this.getDio(sm, ConstraintType.EQ));
                    }
                }
            }
        }

        res1.addAll(this.getDio(constant, ct));
        if (autostrict && ct.equals(ConstraintType.GE)) {
            res2 = new LinkedHashSet<Diophantine>();
            res2.add(this.getAutostrict(constant, ConstraintType.GT));
        }

        return new Pair<Set<Diophantine>, Set<Diophantine>>(res1, res2);
    }

    private Pair<Integer, Integer> getBound(TRSVariable v, Set<LinearTerm> b) {
        for (LinearTerm lt : b) {
            if (lt.getVariables().contains(v)) {
                return new Pair<Integer, Integer>(lt.getCoefficient(v), lt.getConstant());
            }
        }
        return null;
    }

    /* uses PAConstraints to transform an mpt */
    private Pair<Set<LinearTerm>, MatrixParamTerm> doTransformation(Set<LinearTerm> conds, MatrixParamTerm mpt, boolean expandBounded) {
        return this.doTransformationLoop(new SplitCond(conds), mpt, expandBounded);
    }

    private Pair<Set<LinearTerm>, MatrixParamTerm> doTransformationLoop(SplitCond conds, MatrixParamTerm mpt, boolean expandBounded) {
        Pair<SplitCond, MatrixParamTerm> res = this.doTransformationStep(conds, mpt, expandBounded);
        if (res == null) {
            return new Pair<Set<LinearTerm>, MatrixParamTerm>(conds.c1, mpt);
        } else {
            return this.doTransformationLoop(res.x, res.y, expandBounded);
        }
    }

    private Pair<SplitCond, MatrixParamTerm> doTransformationStep(SplitCond conds, MatrixParamTerm mpt, boolean expandBounded) {
        boolean haveDone = false;
        Set<LinearTerm> nc1 = new LinkedHashSet<LinearTerm>(conds.c1);
        Set<LinearTerm> nc2 = new LinkedHashSet<LinearTerm>();
        Set<TRSVariable> nvars = new LinkedHashSet<TRSVariable>(conds.vars);
        Triple<TRSVariable, TRSVariable, LinearTerm> res = null;
        for (LinearTerm lt : conds.c2) {
            if (!haveDone) {
                res = this.isSuitable(lt, conds.vars, expandBounded);
                if (res == null) {
                    nc2.add(lt);
                } else {
                    // got one!
                    haveDone = true;
                    Map<TRSVariable, Integer> mappy = new LinkedHashMap<TRSVariable, Integer>();
                    mappy.put(res.y, Integer.valueOf(1));
                    nc1.add(new LinearTerm(mappy, Integer.valueOf(0)));
                    nvars.add(res.y);
                }
            } else {
                nc2.add(lt);
            }
        }
        if (!haveDone) {
            return null;
        } else {
            nc2 = this.instantiateAll(nc2, res.x, res.z);
            return new Pair<SplitCond, MatrixParamTerm>(new SplitCond(nc1, nc2, nvars), mpt.instantiate(res.x, res.z));
        }
    }

    private Triple<TRSVariable, TRSVariable, LinearTerm> isSuitable(LinearTerm lt, Set<TRSVariable> dont, boolean expandBounded) {
        boolean haveOne = false;
        TRSVariable theVar = null;
        TRSVariable newVar = null;
        LinearTerm binding = null;
        for (TRSVariable v : lt.getVariables()) {
            if (!haveOne && (expandBounded || !dont.contains(v))) {
                Integer i = lt.getCoefficient(v);
                if (Math.abs(i.intValue()) == 1) {
                    // got one!
                    haveOne = true;
                    theVar = v;
                    newVar = TRSTerm.createVariable("!!_" + (Integer.valueOf(this.counter)).toString());
                    this.counter++;
                    binding = this.getBinding(theVar, Integer.signum(i.intValue()), newVar, lt);
                }
            }
        }
        if (!haveOne) {
            return null;
        } else {
            return new Triple<TRSVariable, TRSVariable, LinearTerm>(theVar, newVar, binding);
        }
    }

    private LinearTerm getBinding(TRSVariable theVar, int sign, TRSVariable newVar, LinearTerm lt) {
        Map<TRSVariable, Integer> mappy = new LinkedHashMap<TRSVariable, Integer>();
        int factor = (sign > 0 ? -1 : 1);
        for (TRSVariable v : lt.getVariables()) {
            if (!v.equals(theVar)) {
                mappy.put(v, Integer.valueOf(lt.getCoefficient(v).intValue() * factor));
            }
        }
        mappy.put(newVar, Integer.valueOf(sign));
        Integer newConst = Integer.valueOf(lt.getConstant().intValue() * factor);
        return new LinearTerm(mappy, newConst);
    }

    private Set<LinearTerm> instantiateAll(Set<LinearTerm> lts, TRSVariable x, LinearTerm newx) {
        Set<LinearTerm> res = new LinkedHashSet<LinearTerm>();
        for (LinearTerm lt : lts) {
            res.add(lt.instantiate(x, newx));
        }
        return res;
    }

    private boolean hasIntVars(MatrixParamTerm mpt, Map<TRSVariable, String> varSorts) {
        for (TRSVariable v : mpt.getVariables()) {
            String sort = varSorts.get(v);
            if (sort == null) {
                throw new RuntimeException("Cannot find sort for variable " + v + " in MatrixDioCreator.hasIntVars");
            } else if (sort.equals("int")) {
                return true;
            }
        }
        return false;
    }

    /* output is as above */
    public Pair<Set<Diophantine>, Set<Diophantine>> getDio(MatrixParamTerm mpt, ConstraintType ct, boolean autostrict) {
        // if this.noIntDependence is true, just apply absolute positiveness since we know that all variables are
        // instantiated by natural numbers; otherwise the coefficients have to be zero
        Set<Diophantine> res1 = new LinkedHashSet<Diophantine>();
        Set<Diophantine> res2 = null;

        for (TRSVariable v : mpt.getVariables()) {
            SimpleMatrix sm = mpt.getCoefficient(v);
            if (ct.equals(ConstraintType.EQ)) {
                res1.addAll(this.getDio(sm, ConstraintType.EQ));
            } else {
                res1.addAll(this.getDio(sm, ConstraintType.GE));
            }
        }

        res1.addAll(this.getDio(mpt.getConstant(), ct));
        if (autostrict && ct.equals(ConstraintType.GE)) {
            res2 = new LinkedHashSet<Diophantine>();
            res2.add(this.getAutostrict(mpt.getConstant(), ConstraintType.GT));
        }

        return new Pair<Set<Diophantine>, Set<Diophantine>>(res1, res2);
    }

    private Set<Diophantine> getDio(SimpleMatrix sm, ConstraintType ct) {
        Set<Diophantine> res = new LinkedHashSet<Diophantine>();
        int dimX = sm.dimX();
        int dimY = sm.dimY();
        for (int x = 0; x < dimX; x++) {
            for (int y = 0; y < dimY; y++) {
                res.add(Diophantine.create(sm.get(x, y), ct));
            }
        }
        return res;
    }

    private Diophantine getAutostrict(SimpleMatrix sm, ConstraintType ct) {
        return Diophantine.create(sm.get(0, 0), ct);
    }

    /*************************************************************************/
    private class SplitCond {
        public Set<LinearTerm> c1;
        public Set<LinearTerm> c2;
        public Set<TRSVariable> vars;

        public SplitCond(Set<LinearTerm> c1, Set<LinearTerm> c2, Set<TRSVariable> vars) {
            this.c1 = c1;
            this.c2 = c2;
            this.vars = vars;
        }

        public SplitCond(Set<LinearTerm> conds) {
            Set<LinearTerm> c1 = new LinkedHashSet<LinearTerm>();
            Set<LinearTerm> c2 = new LinkedHashSet<LinearTerm>();
            Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>();

            for (LinearTerm lt : conds) {
                if (lt.isUnivariate()) {
                    if (!vars.containsAll(lt.getVariables())) {
                        c1.add(lt.strengthen());
                        vars.addAll(lt.getVariables());
                    }
                } else {
                    c2.add(lt);
                }
            }

            this.c1 = c1;
            this.c2 = c2;
            this.vars = vars;
        }

    }

}
