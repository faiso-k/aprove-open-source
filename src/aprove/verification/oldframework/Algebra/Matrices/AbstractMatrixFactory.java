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
 * Creates certain often-used matrices, such as
 * matrices for variables or coefficient matrices
 * Also creates a list of elements for which to search for
 * orders.
 *
 * Allows to implement multiple
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public abstract class AbstractMatrixFactory implements MatrixFactory {

    @Override
    public abstract Matrix createNullMatrix();
    @Override
    public abstract Matrix createDPNullMatrix();
    @Override
    public abstract Matrix createVariableMatrix(String name);
    @Override
    public abstract Matrix createArgSymCoefficientMatrix(String name);
    @Override
    public abstract Matrix createDPArgSymCoefficientMatrix(String name);
    @Override
    public abstract Matrix createFSymCoefficientMatrix(String name);
    @Override
    public abstract Matrix createDPFSymCoefficientMatrix(String name);

    @Override
    public abstract Matrix interpretDP(Matrix DPSymInterpretation, Matrix ArgumentInterpretation);
    @Override
    public abstract Matrix interpretFApp(Matrix FSymInterpretation, Matrix ArgumentInterpretation);
    @Override
    public abstract Matrix interpretArg(Matrix ArgSymInterpretation, Matrix Interpretation);
    @Override
    public abstract Matrix interpretDPArg(Matrix ArgSymInterpretation, Matrix Interpretation);

    @Override
    public abstract Collection<? extends VarPolyConstraint> getConstraints(Matrix interL, Matrix interR, ConstraintType type);
    @Override
    public abstract Collection<? extends VarPolyConstraint> getDPConstraints(Matrix interL, Matrix interR);

    @Override
    public abstract Matrix createDiagonalMatrix(String name);

    private final List<SimplePolynomial> coefficients = new ArrayList<SimplePolynomial>();
    private final Set<String> zeroHeuristics = new LinkedHashSet<String>();

    @Override
    public String proofAddition(final Export_Util o, final Map<String, BigInteger> output) {
        return o.export("We used a basic matrix type which is not further parametrizeable.") + o.newline();
    }


    protected void addCoefficient(final SimplePolynomial coefficient) {
        this.coefficients.add (coefficient);
    }

    @Override
    public Collection<? extends SimplePolyConstraint> getCoeffConstraints() {
        final Set<SimplePolyConstraint> result = new LinkedHashSet<SimplePolyConstraint>(this.coefficients.size());
        for (final SimplePolynomial coeff: this.coefficients) {
            result.add(new SimplePolyConstraint(coeff, ConstraintType.GE));
        }
        return result;
    }

    @Override
    public Set<VarPolyConstraint> getExtraConstraints(final TermInterpretor ti, final Set<FunctionSymbol> RcupPsignature) {
        return ti.getExtraConstraints();
    }

    @Override
    public boolean supportsNonLinear() {
        return false;
    }

    @Override
    public Matrix interpretArgMulti(final Matrix argSym, final Matrix[] interpretatios) {
        return null;
    }
    @Override
    public Matrix interpretDPArgMulti(final Matrix DPArgSym, final Matrix[] interpretatios) {
        return null;
    }

    @Override
    public boolean isTotalOrder() {
        return false;
    }

    @Override
    public Set<String> getZeroHeuristics() {
        return this.zeroHeuristics;
    }

    protected void addAssumeZero(final String varname) {
        this.zeroHeuristics.add(varname);
    }

    @Override
    public boolean hasSpecialOrder() {
        return false;
    }

    @Override
    public boolean isGT(final Matrix left, final Matrix right) {
        return left.isGT(right);
    }

    @Override
    public boolean isGE(final Matrix left, final Matrix right) {
        return left.isGE(right);
    }
    @Override
    public QActiveOrder getOrder(final SymbolRepresentations representation, final TermInterpretor ti, final Map<String, BigInteger> result, final Map<Constraint<TRSTerm>, Collection<Constraint<TRSTerm>>> hardCodedRelations, final ActiveResolver activeResolver) {
        return MATRO.create(representation, ti, result, hardCodedRelations, activeResolver);
    }

    @Override
    public boolean supportsArbitraryQDP() {
        return true;
    }
}

