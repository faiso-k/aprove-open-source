package aprove.verification.oldframework.Algebra.Matrices.Interpretation;

import java.util.*;

import aprove.verification.oldframework.Algebra.Matrices.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * This interprets Arguments the usual, linear way.
 * @author Patrick Kabasci
 * @version $Id$
 */
public class LinearArgumentInterpretor extends ArgumentInterpretor {


    public LinearArgumentInterpretor() {

    }

    private LinearArgumentInterpretor(TermInterpretor ti) {
        this.ti = ti;
    }

    @Override
    public ArgumentInterpretor duplicateSelf() {
        return new LinearArgumentInterpretor(this.ti);
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
    public List<Matrix> getDPFAppInterpretations(
            Matrix[] argumentInterpretations, FunctionSymbol fSym,
            MatrixFactory fact, int i) {

        List<Matrix> retVal = new ArrayList<Matrix>(argumentInterpretations.length);

        retVal.add(fact.interpretDPArg(this.ti.getRepresentations().functionArgSyms.get(fSym).get(i), argumentInterpretations[i]));


        return retVal;
    }


    @Override
    public List<Matrix> getFAppInterpretations(
            Matrix[] argumentInterpretations, FunctionSymbol fSym,
            MatrixFactory fact) {

        List<Matrix> retVal = new ArrayList<Matrix>(argumentInterpretations.length);
        for (int i = 0; i < argumentInterpretations.length; i++) {

            retVal.add(fact.interpretArg(this.ti.getRepresentations().functionArgSyms.get(fSym).get(i), argumentInterpretations[i]));

        }

        return retVal;
    }

    @Override
    public List<Matrix> getFAppInterpretations(
            Matrix[] argumentInterpretations, FunctionSymbol fSym,
            MatrixFactory fact, int i) {

        List<Matrix> retVal = new ArrayList<Matrix>(argumentInterpretations.length);

        retVal.add(fact.interpretArg(this.ti.getRepresentations().functionArgSyms.get(fSym).get(i), argumentInterpretations[i]));


        return retVal;
    }

    @Override
    public boolean isApplicable(MatrixFactory fact) {
        // Every factory has to support linear interpretation.
        return true;
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
        return ret;

    }

}

