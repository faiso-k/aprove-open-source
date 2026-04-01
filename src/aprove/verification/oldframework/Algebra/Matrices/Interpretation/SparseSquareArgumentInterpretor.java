package aprove.verification.oldframework.Algebra.Matrices.Interpretation;

import java.util.*;

import aprove.verification.oldframework.Algebra.Matrices.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Interprets (x,y,z,...) as
 * M1.||x|| M1_2.||y|| + ...
 *
 * and (x,y) additionally as
 * ... + Mxy.||x||.||y|| + Myx.||y||.||x||
 *
 * Furthermore for unary symbols also (x) is interpreted as
 * Mx.||x|| + Mxx.||x||.||x||
 * if allowUnarySquares = true
 *
 *
 *
 * Requires NonLinear-able factory, also does not care about factory's implementation
 * of interpretArg, simply replaces it with the pairs. Note that DP interpretation is
 * not modified.
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public class SparseSquareArgumentInterpretor extends ArgumentInterpretor {

    private boolean useUnary = false;


    public void setUseUnary(boolean newUseUnary) {
        this.useUnary = newUseUnary;
    }

    public SparseSquareArgumentInterpretor() {

    }

    private SparseSquareArgumentInterpretor(TermInterpretor ti, boolean useUnary) {
        this.ti = ti;
        this.useUnary = useUnary;
    }

    @Override
    public ArgumentInterpretor duplicateSelf() {
        return new SparseSquareArgumentInterpretor(this.ti, this.useUnary);
    }



    @Override
    public List<Matrix> getDPFAppInterpretations(
            Matrix[] argumentInterpretations, FunctionSymbol sym,
            MatrixFactory fact, int i) {
        List<Matrix> retVal = new ArrayList<Matrix>(argumentInterpretations.length);

        retVal.add(fact.interpretDPArg(this.ti.getRepresentations().functionArgSyms.get(sym).get(i), argumentInterpretations[i]));



        retVal.addAll(this.ti.getRepresentations().multifArgSyms.get(sym).values());


        return retVal;
    }

    @Override
    public List<Matrix> getFAppInterpretations(
            Matrix[] argumentInterpretations, FunctionSymbol sym,
            MatrixFactory fact, int i) {


        List<Matrix> retVal = new ArrayList<Matrix>(argumentInterpretations.length);

        retVal.add(fact.interpretArg(this.ti.getRepresentations().functionArgSyms.get(sym).get(i), argumentInterpretations[i]));



        // The non-linear matrices forbid posFiltering.

        retVal.addAll(this.ti.getRepresentations().multifArgSyms.get(sym).values());



        return retVal;
    }

    @Override
    public List<Matrix> getDPFAppInterpretations(
            Matrix[] argumentInterpretations, FunctionSymbol fSym,
            MatrixFactory fact) {

        List<Matrix> retVal = new ArrayList<Matrix>(argumentInterpretations.length);
        for (int i = 0; i < argumentInterpretations.length; i++) {

            retVal.add(fact.interpretDPArg(this.ti.getRepresentations().functionArgSyms.get(fSym).get(i), argumentInterpretations[i]));

        }

        return retVal;
    }

    @Override
    public List<Matrix> getFAppInterpretations(
            Matrix[] argumentInterpretations, FunctionSymbol fSym,
            MatrixFactory fact) {

        List<Matrix> retVal = new ArrayList<Matrix>(argumentInterpretations.length);
        for (int i = 0; i < argumentInterpretations.length; i++) {

            retVal.add(this.ti.getRepresentations().functionArgSyms.get(fSym).get(i).multiplyRight(argumentInterpretations[i]));

        }

        if (argumentInterpretations.length == 2) {
            retVal.add(this.getRightMatrix(fSym, 1, fact).multiplyRight(argumentInterpretations[0]).multiplyRight(argumentInterpretations[1]));
            retVal.add(this.getRightMatrix(fSym, 2, fact).multiplyRight(argumentInterpretations[1]).multiplyRight(argumentInterpretations[0]));

        } else if (argumentInterpretations.length == 1 && this.useUnary) {
            retVal.add(this.getRightMatrix(fSym, 1, fact).multiplyRight(argumentInterpretations[0]).multiplyRight(argumentInterpretations[0]));
        }

        return retVal;
    }


    private Matrix getRightMatrix(FunctionSymbol fSym, int arg, MatrixFactory fact) {
        Map<String, Matrix> fArgSyms = this.ti.getRepresentations().multifArgSyms.get(fSym);
        String uid = fSym.getName() + "_{" + Integer.toString(arg-1) + "," + Integer.toString(1 - (arg-1)) + "}";
        if (!fArgSyms.containsKey(uid)) {
            fArgSyms.put(uid, fact.createArgSymCoefficientMatrix(fSym.toString() + uid));
        }
        return fArgSyms.get(uid);
    }


    @Override
    public List<SimplePolynomial> getFSymCoefficients(FunctionSymbol fSym, int argNr, MatrixFactory fact) {
        // Not much work here, simply return all (filtered) entries of the coefficient matrix
        List<SimplePolynomial> ret = new ArrayList<SimplePolynomial>();
        Matrix mat;
        mat = this.ti.getRepresentations().functionArgSyms.get(fSym).get(argNr);
        List<VarPolynomial> tmp = new ArrayList<VarPolynomial>();

        tmp = mat.getList();
        for (VarPolynomial v: tmp) {
            ret.addAll(v.getCoefficientsOfVariables());
            ret.add(v.getConstantPart());
        }

        if ((this.useUnary && fSym.getArity() == 1) || fSym.getArity() == 2) {
            mat = this.getRightMatrix(fSym, argNr, fact);
            tmp = mat.getList();
            for (VarPolynomial v: tmp) {
                ret.addAll(v.getCoefficientsOfVariables());
                ret.add(v.getConstantPart());
            }
        }

        return ret;

    }


    @Override
    public boolean isApplicable(MatrixFactory fact) {
        return fact.supportsNonLinear();
    }

}

