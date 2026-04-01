package aprove.verification.oldframework.Algebra.Matrices;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.Algebra.Matrices.Interpretation.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 *
 * @author kabasci
 * @version $Id$
 */
public interface MatrixFactory {

    public abstract Matrix Unity();

    public abstract Matrix createDPNullMatrix();

    public abstract Matrix createNullMatrix();

    public abstract Matrix createVariableMatrix(String name);

    public abstract Matrix createArgSymCoefficientMatrix(String name);

    public abstract Matrix createDPArgSymCoefficientMatrix(String name);

    public abstract Matrix createFSymCoefficientMatrix(String name);

    public abstract Matrix createDPFSymCoefficientMatrix(String name);

    public abstract Matrix interpretDP(Matrix DPSymInterpretation,
            Matrix ArgumentInterpretation);

    public abstract Matrix interpretFApp(Matrix FSymInterpretation,
            Matrix ArgumentInterpretation);

    public abstract Matrix interpretArg(Matrix ArgSymInterpretation,
            Matrix Interpretation);

    public abstract Matrix interpretDPArg(Matrix ArgSymInterpretation,
            Matrix Interpretation);

    public abstract String proofAddition(Export_Util o, Map<String, BigInteger> output);

    public abstract Collection<? extends VarPolyConstraint> getConstraints(Matrix interL, Matrix interR, ConstraintType type);
    public abstract Collection<? extends VarPolyConstraint> getDPConstraints(Matrix interL, Matrix interR);
    public abstract Collection<? extends SimplePolyConstraint> getCoeffConstraints();
    public abstract Set<? extends VarPolyConstraint> getExtraConstraints(TermInterpretor ti, Set<FunctionSymbol> nonTupleSignature);
    public abstract Set<String> getZeroHeuristics();

    // Can we have P-ROOT-Symbols occurring anywhere else?
    public abstract boolean supportsArbitraryQDP();

    public abstract boolean supportsNonLinear();
    public abstract Matrix interpretArgMulti(Matrix ArgSymInterpretation, Matrix[] Interpretations);
    public abstract Matrix interpretDPArgMulti(Matrix ArgSymInterpretation, Matrix[] Interpretations);

    public abstract Matrix createDiagonalMatrix(String string);

    public abstract boolean isTotalOrder();

    public abstract boolean hasSpecialOrder();

    public abstract boolean isGE(Matrix left, Matrix right);
    public abstract boolean isGT(Matrix left, Matrix right);
    public QActiveOrder getOrder(SymbolRepresentations representation, TermInterpretor ti, Map<String, BigInteger> result, Map<Constraint<TRSTerm>, Collection<Constraint<TRSTerm>>> hardCodedRelations, ActiveResolver activeResolver);

    public MatrixFactory duplicateSelf();

}
