package aprove.verification.oldframework.Algebra.Matrices;

import java.util.*;
import java.util.logging.*;

import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.Matrices.Filters.*;
import aprove.verification.oldframework.Algebra.Matrices.Filters.MatrixFilter.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * This matrix factory represents DPs as numbers, FApps and Arguments with
 * full matrices as representors.
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public class CollapsingDPFullMatrixFactory extends CollapsingDPMatrixFactory {

    Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Matrices.CollapsingDPFullMatrixFactory");

    private final int dimension;

    private final MatrixFilter filter;

    @ParamsViaArgumentObject
    public CollapsingDPFullMatrixFactory(Arguments arguments) {
        this.filter = arguments.filter;
        this.dimension = arguments.size;
    }

    private CollapsingDPFullMatrixFactory(int dimension, MatrixFilter filter) {
        this.dimension = dimension;
        this.filter = filter;
    }



    @Override
    public MatrixFactory duplicateSelf() {

        // Warning! If filters get too sophisticated, this as well might raise problems (then duplicateSelf for filters is required)
        // Currently, this is ok.
        return new CollapsingDPFullMatrixFactory(this.dimension, this.filter);

    }


    @Override
    public Matrix createArgSymCoefficientMatrix(String name) {
        return this.createFullMatrix(name);
    }

    @Override
    public Matrix createDPFSymCoefficientMatrix(String name) {
        return this.createOneByOneMatrix(name);
    }

    @Override
    public Matrix createFSymCoefficientMatrix(String name) {
        return this.createFullMatrix(name);
    }

    @Override
    public Matrix createVariableMatrix(String name) {
        VarPolynomial[][] result = new VarPolynomial[this.dimension][this.dimension];

        for (int i=0; i < this.dimension; i++) {
            for (int j=0; j < this.dimension; j++) {
                result[i][j] = VarPolynomial.createVariable(name + i + ","+ j);
            }
        }
        return new Matrix(result);
    }


    private Matrix createTwoColTuple(String name) {
        VarPolynomial[][] result = new VarPolynomial[this.dimension][2];

        for (int i=0; i < this.dimension; i++) {

            SimplePolynomial simplePoly = SimplePolynomial.create(name + i);
            result[i][0] = VarPolynomial.create(simplePoly);
            super.addCoefficient(simplePoly);

        }
        for (int i=0; i < this.dimension; i++) {

            SimplePolynomial simplePoly = SimplePolynomial.create(name + i + "_");
            result[i][1] = VarPolynomial.create(simplePoly);
            super.addCoefficient(simplePoly);

        }
        return new Matrix(result);
    }

    private Matrix createFullMatrix(String name) {
        VarPolynomial[][] result = new VarPolynomial[this.dimension][this.dimension];

        for (int i=0; i < this.dimension; i++) {
            for (int j=0; j < this.dimension; j++) {
                MatrixFilter.Filtermode res = this.filter.filterCoefficient(this.dimension, i, j);
                if (res == Filtermode.FULLRANGE) {
                    SimplePolynomial simplePoly = SimplePolynomial.create(name + i + "," + j);
                    result[i][j] = VarPolynomial.create(simplePoly);
                    super.addCoefficient(simplePoly);
                } else if (res == Filtermode.UNITYORZERO) {
                    SimplePolynomial simplePoly = SimplePolynomial.create(name + i + "," + j);
                    result[i][j] = VarPolynomial.create(simplePoly);
                    super.addCoefficient(simplePoly);
                } else {
                    SimplePolynomial simplePoly = SimplePolynomial.ZERO;
                    result[i][j] = VarPolynomial.create(simplePoly);
                }
            }
        }
        return new Matrix(result);
    }

    @Override
    public Matrix createDiagonalMatrix(String name) {
        VarPolynomial[][] result = new VarPolynomial[this.dimension][this.dimension];

        for (int i=0; i < this.dimension; i++) {
            for (int j=0; j < this.dimension; j++) {
                if (i==j)  {
                    MatrixFilter.Filtermode res = this.filter.filterCoefficient(this.dimension, i, j);
                    if (res == Filtermode.FULLRANGE) {
                        SimplePolynomial simplePoly = SimplePolynomial.create(name + i + "," + j);
                        result[i][j] = VarPolynomial.create(simplePoly);
                        super.addCoefficient(simplePoly);
                    } else if (res == Filtermode.UNITYORZERO) {
                        SimplePolynomial simplePoly = SimplePolynomial.create(name + i + "," + j);
                        result[i][j] = VarPolynomial.create(simplePoly);
                        super.addCoefficient(simplePoly);
                    } else {
                        SimplePolynomial simplePoly = SimplePolynomial.ZERO;
                        result[i][j] = VarPolynomial.create(simplePoly);
                    }
                } else {
                    SimplePolynomial simplePoly = SimplePolynomial.ZERO;
                    result[i][j] = VarPolynomial.create(simplePoly);
                }
            }
        }
        return new Matrix(result);
    }


    @Override
    public Matrix Unity() {
        VarPolynomial[][] result = new VarPolynomial[this.dimension][this.dimension];

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

    private Matrix createOneByOneMatrix(String name) {
        VarPolynomial[][] result = new VarPolynomial[1][1];

        SimplePolynomial simplePoly = SimplePolynomial.create(name);
        result[0][0] = VarPolynomial.create(simplePoly);
        super.addCoefficient(simplePoly);
        return new Matrix(result);
    }




    @Override
    public Matrix createDPArgSymCoefficientMatrix(String name) {
        return this.createTwoColTuple(name);
    }

    @Override
    public Matrix interpretDPArg(Matrix ArgSymInterpretation,
            Matrix Interpretation) {
        Matrix temp = ArgSymInterpretation.getCol(0).multiplyLeft(Interpretation);
        return ArgSymInterpretation.getCol(1).transpose().multiplyRight(temp);
    }

    @Override
    public Set<VarPolyConstraint> getConstraints(Matrix interL, Matrix interR, ConstraintType type) {

        Set<VarPolyConstraint> constraints = new LinkedHashSet<VarPolyConstraint>(this.dimension*this.dimension);

        // For full matrices, we need to generate one constraint for each matrix element.
        for (int i=0; i < interL.getNumRows(); i++) {
            for (int j=0; j < interR.getNumCols(); j++) {
                constraints.add(new VarPolyConstraint(interL.get(i, j).minus(interR.get(i, j)), type));
            }
        }

        return constraints;

    }


    @Override
    public Set<VarPolyConstraint> getDPConstraints(Matrix interL, Matrix interR) {

        Set<VarPolyConstraint> constraints = new LinkedHashSet<VarPolyConstraint>(this.dimension*this.dimension);

        for (int i=0; i < interL.getNumRows(); i++) {
            for (int j=0; j < interR.getNumCols(); j++) {
                constraints.add(new VarPolyConstraint(interL.get(i, j).minus(interR.get(i, j)), ConstraintType.GE));
            }
        }

        return constraints;

    }


    @Override
    public Matrix createNullMatrix() {
        VarPolynomial[][] result = new VarPolynomial[this.dimension][this.dimension];

        for (int i=0; i < this.dimension; i++) {
            for (int j=0; j < this.dimension; j++) {
                result[i][j] = VarPolynomial.ZERO;
            }
        }
        return new Matrix(result);
    }

    @Override
    public Matrix createDPNullMatrix() {
        VarPolynomial[][] result = new VarPolynomial[1][1];
        result[0][0] = VarPolynomial.ZERO;
        return new Matrix(result);
    }

    @Override
    public boolean supportsNonLinear() {
        return true;
    }

    @Override
    public Matrix interpretDPArgMulti(Matrix DPArgSym, Matrix[] interpretations) {
        Matrix temp;
        temp = DPArgSym.getCol(0).transpose().multiplyRight(interpretations);

        return temp.multiplyRight(DPArgSym.getCol(1));

    }


    @Override
    public Matrix interpretArgMulti(Matrix ArgSym, Matrix[] interpretations) {
        long time = System.currentTimeMillis();
        Matrix temp;
        temp = ArgSym.multiplyRight(interpretations);
        this.log.log(Level.FINEST, "Multiplying arguments took " + Long.toString(System.currentTimeMillis() - time) + "ms\n");
        return temp;

    }

    public int getSize() {
        return this.dimension;
    }

    public MatrixFilter getFilter() {
        return this.filter;
    }

    public static class Arguments {
        public MatrixFilter filter;
        public int size;
    }

}

