package aprove.verification.oldframework.Algebra.Matrices.Interpretation;

import java.util.*;

import aprove.verification.oldframework.Algebra.Matrices.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * This class interprets Arguments. There will be several different methods to do this
 * e.g. linear, simple/mixed etc.
 * The main difference is in whether our generated matrix polynomials will be linear in their
 * coefficients (all MatrixFactories support this type) or of some other kind.
 * @author Patrick Kabasci
 * @version $Id$
 */
public abstract class ArgumentInterpretor {

    protected TermInterpretor ti;

    public abstract List<Matrix> getFAppInterpretations(Matrix[] argumentInterpretations, FunctionSymbol fSym, MatrixFactory fact);
    public abstract List<Matrix> getDPFAppInterpretations(Matrix[] argumentInterpretations, FunctionSymbol fSym, MatrixFactory fact);

    // Only get those interpretations regarding the ith argument. Neccesary for position filtering.
    public abstract List<Matrix> getFAppInterpretations(Matrix[] argumentInterpretations, FunctionSymbol fSym, MatrixFactory fact, int i);
    public abstract List<Matrix> getDPFAppInterpretations(Matrix[] argumentInterpretations, FunctionSymbol fSym, MatrixFactory fact, int i);

    public abstract List<SimplePolynomial> getFSymCoefficients(FunctionSymbol fSym, int argNr,MatrixFactory fact);

    public Set<VarPolyConstraint> getExtraConstraints() {
        return new LinkedHashSet<VarPolyConstraint>();
    }

    public abstract boolean isApplicable(MatrixFactory fact);
    public void setTermInterpretor(final TermInterpretor interpretor) {
        this.ti = interpretor;
    }

    // Evil Hack due to strategz problem
    public abstract ArgumentInterpretor duplicateSelf();


}

