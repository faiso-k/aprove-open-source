package aprove.verification.oldframework.Algebra.Matrices;

import java.util.*;

import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.Matrices.Filters.*;
import aprove.verification.oldframework.Algebra.Matrices.Filters.MatrixFilter.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * This MatrixFactory implements interpretations as in the IJCAR 06 paper.
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public class CollapsingDPTupleVariablesMatrixFactory extends AbstractMatrixFactory {

    private final int dimension;

    private final MatrixFilter filter;

    @ParamsViaArgumentObject
    public CollapsingDPTupleVariablesMatrixFactory(final Arguments arguments) {
        this.filter = arguments.filter;
        this.dimension = arguments.size;
    }

    private CollapsingDPTupleVariablesMatrixFactory(final int dimension, final MatrixFilter filter) {
        this.dimension = dimension;
        this.filter = filter;
    }



    @Override
    public MatrixFactory duplicateSelf() {

        // Warning! If filters get too sophisticated, this as well might raise problems (then duplicateSelf for filters is required)
        // Currently, this is ok.
        return new CollapsingDPTupleVariablesMatrixFactory(this.dimension, this.filter);

    }

    @Override
    public Matrix Unity() {
        final VarPolynomial[][] result = new VarPolynomial[this.dimension][this.dimension];

        for (int i=0; i < this.dimension; i++) {
            for (int j=0; j < this.dimension; j++) {
                if (i==j) {
                    result[i][j] = VarPolynomial.ONE;
                } else {
                    result[i][j] = VarPolynomial.ZERO;
                }
            }
        }
        return new Matrix(result);
    }

    @Override
    public Matrix createDiagonalMatrix(final String name) {
        final VarPolynomial[][] result = new VarPolynomial[this.dimension][this.dimension];

        for (int i=0; i < this.dimension; i++) {
            for (int j=0; j < this.dimension; j++) {
                if (i==j)  {
                    final MatrixFilter.Filtermode res = this.filter.filterCoefficient(this.dimension, i, j);
                    if (res == Filtermode.FULLRANGE) {
                        final SimplePolynomial simplePoly = SimplePolynomial.create(name + i + "," + j);
                        result[i][j] = VarPolynomial.create(simplePoly);
                        super.addCoefficient(simplePoly);
                    } else if (res == Filtermode.UNITYORZERO) {
                        final SimplePolynomial simplePoly = SimplePolynomial.create(name + i + "," + j);
                        result[i][j] = VarPolynomial.create(simplePoly);
                        super.addCoefficient(simplePoly);
                    } else if (res == Filtermode.ASSUMEZERO) {
                        final SimplePolynomial simplePoly = SimplePolynomial.create(name + i + "," + j);
                        result[i][j] = VarPolynomial.create(simplePoly);
                        super.addCoefficient(simplePoly);
                        super.addAssumeZero(name + i + "," + j);
                    } else {
                        final SimplePolynomial simplePoly = SimplePolynomial.ZERO;
                        result[i][j] = VarPolynomial.create(simplePoly);
                    }
                } else {
                    final SimplePolynomial simplePoly = SimplePolynomial.ZERO;
                    result[i][j] = VarPolynomial.create(simplePoly);
                }
            }
        }
        return new Matrix(result);
    }

    @Override
    public Matrix interpretArg(final Matrix ArgSymInterpretation,
            final Matrix Interpretation) {
        return ArgSymInterpretation.multiplyRight(Interpretation);

    }

    @Override
    public Matrix interpretDPArg(final Matrix ArgSymInterpretation,
            final Matrix Interpretation) {
        return ArgSymInterpretation.multiplyRight(Interpretation);

    }

    @Override
    public Matrix interpretDP(final Matrix DPSymInterpretation,
            final Matrix ArgumentInterpretation) {

        return DPSymInterpretation.add(ArgumentInterpretation);

    }

    @Override
    public Matrix interpretFApp(final Matrix FSymInterpretation,
            final Matrix ArgumentInterpretation) {

        return FSymInterpretation.add(ArgumentInterpretation);
    }

    @Override
    public Matrix createArgSymCoefficientMatrix(final String name) {
        return this.createFullMatrix(name);
    }

    @Override
    public Matrix createDPFSymCoefficientMatrix(final String name) {
        return this.createOneByOneMatrix(name);
    }

    @Override
    public Matrix createFSymCoefficientMatrix(final String name) {
        return this.createColTuple(name);
    }

    @Override
    public Matrix createVariableMatrix(final String name) {
        final VarPolynomial[][] result = new VarPolynomial[this.dimension][1];

        for (int i = 0; i < this.dimension; i++) {
            result[i][0] = VarPolynomial.createVariable(name + i);
        }
        return new Matrix(result);
    }

    private Matrix createColTuple(final String name) {
        final VarPolynomial[][] result = new VarPolynomial[this.dimension][1];

        for (int i = 0; i < this.dimension; i++) {

            final SimplePolynomial simplePoly = SimplePolynomial.create(name + i);
            result[i][0] = VarPolynomial.create(simplePoly);
            super.addCoefficient(simplePoly);

        }
        return new Matrix(result);
    }

    private Matrix createFullMatrix(final String name) {
        final VarPolynomial[][] result = new VarPolynomial[this.dimension][this.dimension];

        for (int i=0; i < this.dimension; i++) {
            for (int j=0; j < this.dimension; j++) {
                final MatrixFilter.Filtermode res = this.filter.filterCoefficient(this.dimension, i, j);
                if (res == Filtermode.FULLRANGE) {
                    final SimplePolynomial simplePoly = SimplePolynomial.create(name + i + "," + j);
                    result[i][j] = VarPolynomial.create(simplePoly);
                    super.addCoefficient(simplePoly);
                } else if (res == Filtermode.UNITYORZERO) {
                    final SimplePolynomial simplePoly = SimplePolynomial.create(name + i + "," + j);
                    result[i][j] = VarPolynomial.create(simplePoly);
                    super.addCoefficient(simplePoly);
                } else {
                    final SimplePolynomial simplePoly = SimplePolynomial.ZERO;
                    result[i][j] = VarPolynomial.create(simplePoly);
                }
            }
        }
        return new Matrix(result);
    }



    private Matrix createRowTuple(final String name) {
        final VarPolynomial[][] result = new VarPolynomial[1][this.dimension];

        for (int i = 0; i < this.dimension; i++) {

            final SimplePolynomial simplePoly = SimplePolynomial.create(name + i);
            result[0][i] = VarPolynomial.create(simplePoly);
            super.addCoefficient(simplePoly);

        }
        return new Matrix(result);
    }

    private Matrix createOneByOneMatrix(final String name) {
        final VarPolynomial[][] result = new VarPolynomial[1][1];

        final SimplePolynomial simplePoly = SimplePolynomial.create(name);
        result[0][0] = VarPolynomial.create(simplePoly);
        super.addCoefficient(simplePoly);
        return new Matrix(result);
    }

    @Override
    public Matrix createDPArgSymCoefficientMatrix(final String name) {
        return this.createRowTuple(name);
    }

    @Override
    public Set<VarPolyConstraint> getConstraints(final Matrix interL, final Matrix interR, final ConstraintType type) {

        final Set<VarPolyConstraint> constraints = new LinkedHashSet<VarPolyConstraint>(this.dimension*this.dimension);

        // For full matrices, we need to generate one constraint for each matrix element.
        for (int i=0; i < interL.getNumRows(); i++) {
            for (int j=0; j < interR.getNumCols(); j++) {
                constraints.add(new VarPolyConstraint(interL.get(i, j).minus(interR.get(i, j)), type));
            }
        }

        return constraints;

    }

    @Override
    public Set<VarPolyConstraint> getDPConstraints(final Matrix interL, final Matrix interR) {

        final Set<VarPolyConstraint> constraints = new LinkedHashSet<VarPolyConstraint>(
                this.dimension * this.dimension);

        for (int i = 0; i < interL.getNumRows(); i++) {
            for (int j = 0; j < interR.getNumCols(); j++) {
                constraints.add(new VarPolyConstraint(interL.get(i, j).minus(
                        interR.get(i, j)), ConstraintType.GE));
            }
        }

        return constraints;

    }

    @Override
    public Matrix createNullMatrix() {
        final VarPolynomial[][] result = new VarPolynomial[this.dimension][1];

        for (int i = 0; i < this.dimension; i++) {
            result[i][0] = VarPolynomial.ZERO;
        }
        return new Matrix(result);
    }

    @Override
    public Matrix createDPNullMatrix() {
        final VarPolynomial[][] result = new VarPolynomial[1][1];

        result[0][0] = VarPolynomial.ZERO;
        return new Matrix(result);
    }

    public int getSize() {
        return this.dimension;
    }

    public MatrixFilter getFilter() {
        return this.filter;
    }

    // This implementation is total iff. 1x1
    @Override
    public boolean isTotalOrder() {
        return this.dimension == 1;
    }

    public static class Arguments {
        public MatrixFilter filter;
        public int size;
    }

}

