package aprove.verification.oldframework.Algebra.Matrices;

import java.math.*;
import java.util.*;

import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.Matrices.Filters.*;
import aprove.verification.oldframework.Algebra.Matrices.Filters.MatrixFilter.*;
import aprove.verification.oldframework.Algebra.Matrices.Interpretation.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * This MatrixFactory implements interpretations which ensure polynomial complexity traces.
 *
 * @author Patrick Kabasci
 */
public class PolynomialComplexityMatrixFactory extends AbstractMatrixFactory {

    private final int dimension;

    private final MatrixFilter constructorFilter;
    private final MatrixFilter definedFilter;

    public final Set<VarPolyConstraint> extraConstraints = new LinkedHashSet<VarPolyConstraint>();

    @ParamsViaArgumentObject
    public PolynomialComplexityMatrixFactory(Arguments arguments) {
        this.constructorFilter = new UpperTriangleDiagonalOneFilter();
        //this.definedFilter = new UpperTriangleFilter();
        this.definedFilter = new FullMatrixFilter();
        this.dimension = arguments.size;
    }

    public PolynomialComplexityMatrixFactory(int dimension) {
        this.dimension = dimension;
        this.constructorFilter = new UpperTriangleDiagonalOneFilter();
        this.definedFilter = new UpperTriangleFilter();
    }

    @Override
    public Set<VarPolyConstraint> getExtraConstraints(final TermInterpretor ti, final Set<FunctionSymbol> RcupPsignature) {
        Set<VarPolyConstraint> extraC = ti.getExtraConstraints();
        extraC.addAll(this.extraConstraints);
        return extraC;
    }

    @Override
    public MatrixFactory duplicateSelf() {

        // Warning! If filters get too sophisticated, this as well might raise problems (then duplicateSelf for filters is required)
        // Currently, this is ok.
        return new PolynomialComplexityMatrixFactory(this.dimension);

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
    @Override
    public Matrix createDiagonalMatrix(String name) {
        VarPolynomial[][] result = new VarPolynomial[this.dimension][this.dimension];

        for (int i=0; i < this.dimension; i++) {
            for (int j=0; j < this.dimension; j++) {
                if (i==j)  {
                    MatrixFilter.Filtermode res = this.constructorFilter.filterCoefficient(this.dimension, i, j);
                    if (res == Filtermode.FULLRANGE) {
                        SimplePolynomial simplePoly = SimplePolynomial.create(name + i + "," + j);
                        result[i][j] = VarPolynomial.create(simplePoly);
                        super.addCoefficient(simplePoly);
                    } else if (res == Filtermode.UNITYORZERO) {
                        SimplePolynomial simplePoly = SimplePolynomial.create(name + i + "," + j);
                        result[i][j] = VarPolynomial.create(simplePoly);
                        this.extraConstraints.add(new VarPolyConstraint(
                            VarPolynomial.create(
                                simplePoly.times(BigInteger.valueOf(-1l)).plus(SimplePolynomial.create(BigInteger.ONE)
                            )), ConstraintType.GE));
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
    public Matrix interpretArg(Matrix ArgSymInterpretation,
            Matrix Interpretation) {
        return ArgSymInterpretation.multiplyRight(Interpretation);

    }

    @Override
    public Matrix interpretDPArg(Matrix ArgSymInterpretation,
            Matrix Interpretation) {
        return ArgSymInterpretation.multiplyRight(Interpretation);

    }

    @Override
    public Matrix interpretDP(Matrix DPSymInterpretation,
            Matrix ArgumentInterpretation) {

        return DPSymInterpretation.add(ArgumentInterpretation);

    }

    @Override
    public Matrix interpretFApp(Matrix FSymInterpretation,
            Matrix ArgumentInterpretation) {

        return FSymInterpretation.add(ArgumentInterpretation);
    }

    @Override
    public Matrix createArgSymCoefficientMatrix(String name) {
        return this.createFullMatrix(name);
    }

    @Override
    public Matrix createDPFSymCoefficientMatrix(String name) {
        return this.createColTuple(name);
    }

    @Override
    public Matrix createFSymCoefficientMatrix(String name) {
        return this.createColTuple(name);
    }

    @Override
    public Matrix createVariableMatrix(String name) {
        VarPolynomial[][] result = new VarPolynomial[this.dimension][1];

        for (int i = 0; i < this.dimension; i++) {
            result[i][0] = VarPolynomial.createVariable(name + i);
        }
        return new Matrix(result);
    }

    private Matrix createColTuple(String name) {
        VarPolynomial[][] result = new VarPolynomial[this.dimension][1];

        for (int i = 0; i < this.dimension; i++) {

            SimplePolynomial simplePoly = SimplePolynomial.create(name + i);
            result[i][0] = VarPolynomial.create(simplePoly);
            super.addCoefficient(simplePoly);

        }
        return new Matrix(result);
    }

    private Matrix createFullMatrix(String name) {
        VarPolynomial[][] result = new VarPolynomial[this.dimension][this.dimension];

        for (int i=0; i < this.dimension; i++) {
            for (int j=0; j < this.dimension; j++) {
                MatrixFilter.Filtermode res = this.constructorFilter.filterCoefficient(this.dimension, i, j);
                if (res == Filtermode.FULLRANGE) {
                    SimplePolynomial simplePoly = SimplePolynomial.create(name + i + "," + j);
                    result[i][j] = VarPolynomial.create(simplePoly);
                    super.addCoefficient(simplePoly);
                } else if (res == Filtermode.UNITYORZERO) {
                    SimplePolynomial simplePoly = SimplePolynomial.create(name + i + "," + j);
                    result[i][j] = VarPolynomial.create(simplePoly);
                    super.addCoefficient(simplePoly);
                    this.extraConstraints.add(new VarPolyConstraint(
                        VarPolynomial.create(
                            simplePoly.times(BigInteger.valueOf(-1l)).plus(SimplePolynomial.create(BigInteger.ONE)
                        )), ConstraintType.GE));
                } else {
                    SimplePolynomial simplePoly = SimplePolynomial.ZERO;
                    result[i][j] = VarPolynomial.create(simplePoly);
                }
            }
        }
        return new Matrix(result);
    }


    public Matrix createDefinedMatrix(String name) {
        VarPolynomial[][] result = new VarPolynomial[this.dimension][this.dimension];

        for (int i=0; i < this.dimension; i++) {
            for (int j=0; j < this.dimension; j++) {
                MatrixFilter.Filtermode res = this.definedFilter.filterCoefficient(this.dimension, i, j);
                if (res == Filtermode.FULLRANGE) {
                    SimplePolynomial simplePoly = SimplePolynomial.create(name + i + "," + j);
                    result[i][j] = VarPolynomial.create(simplePoly);
                    super.addCoefficient(simplePoly);
                } else if (res == Filtermode.UNITYORZERO) {
                    SimplePolynomial simplePoly = SimplePolynomial.create(name + i + "," + j);
                    result[i][j] = VarPolynomial.create(simplePoly);
                    super.addCoefficient(simplePoly);
                    this.extraConstraints.add(new VarPolyConstraint(
                        VarPolynomial.create(
                            simplePoly.times(BigInteger.valueOf(-1l)).plus(SimplePolynomial.create(BigInteger.ONE)
                        )), ConstraintType.GE));
                } else {
                    SimplePolynomial simplePoly = SimplePolynomial.ZERO;
                    result[i][j] = VarPolynomial.create(simplePoly);
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
        return this.createFullMatrix(name);
    }

    @Override
    public Set<VarPolyConstraint> getConstraints(Matrix interL, Matrix interR, ConstraintType type) {

        Set<VarPolyConstraint> constraints = new LinkedHashSet<VarPolyConstraint>(this.dimension*this.dimension);

        // For full matrices, we need to generate one constraint for each matrix element. However on GR, we only need GE for anything else than 0,0.
        for (int i=0; i < interL.getNumRows(); i++) {
            for (int j=0; j < interR.getNumCols(); j++) {
                constraints.add(new VarPolyConstraint(interL.get(i, j).minus(interR.get(i, j)), (type==ConstraintType.GT && i+j > 0)? ConstraintType.GE: type));
            }
        }

        return constraints;

    }

    @Override
    public Set<VarPolyConstraint> getDPConstraints(Matrix interL, Matrix interR) {

        // Only component 1,1 can be used in polynomial complexity.

        Set<VarPolyConstraint> constraints = new LinkedHashSet<VarPolyConstraint>(
                1);

        constraints.add(new VarPolyConstraint(interL.get(0, 0).minus(
                interR.get(0, 0)), ConstraintType.GE));


        return constraints;

    }

    @Override
    public Matrix createNullMatrix() {
        VarPolynomial[][] result = new VarPolynomial[this.dimension][1];

        for (int i = 0; i < this.dimension; i++) {
            result[i][0] = VarPolynomial.ZERO;
        }
        return new Matrix(result);
    }

    @Override
    public Matrix createDPNullMatrix() {
        VarPolynomial[][] result = new VarPolynomial[this.dimension][1];

        for (int i = 0; i < this.dimension; i++) {
            result[i][0] = VarPolynomial.ZERO;
        }
        return new Matrix(result);
    }

    public int getSize() {
        return this.dimension;
    }

    public MatrixFilter getFilter() {
        return this.constructorFilter;
    }

    public static class Arguments {
        public int size;
    }

}
