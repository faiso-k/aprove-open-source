package aprove.verification.oldframework.Algebra.Matrices;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Matrices.Filters.*;
import aprove.verification.oldframework.Algebra.Matrices.Filters.MatrixFilter.*;
import aprove.verification.oldframework.Algebra.Matrices.Interpretation.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * This MatrixFactory implements interpretations as in the IJCAR 06 paper, but allows a lower bound for ground terms, thus
 * interpreting Variables as some x + q where q <= this lower bound.
 *
 * Note that using this Factory is subject to the following limitation:
 *   * There must not be any variable in the TRS named " C". (The " " should prohibit this, though.)
 *
 * It is also adviseable to use a variable renaming transformation first.
 * This turns, for example,
 * the TRS
 *
 * f(g(x),y) -> f(y,x)
 * g(y) -> h(y)
 * h(x) -> a
 *
 * into the equivalent TRS
 *
 * f(g(x_1), x_2) -> f(x_2, x_1)
 * g(x_3) -> h(x_3)
 * h(x_4) -> a
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public class LowerBoundCollapsingDPTupleVariablesMatrixFactory extends AbstractMatrixFactory {

    private final int dimension;
    private final MatrixFilter filter;

    private Map<Integer, ImmutableArrayList<TRSTerm>> cList = new LinkedHashMap<Integer, ImmutableArrayList<TRSTerm>> ();

    private Matrix C;

    private Map<String, Matrix> lessThanEqC = new LinkedHashMap<String, Matrix>();

    @ParamsViaArgumentObject
    public LowerBoundCollapsingDPTupleVariablesMatrixFactory(Arguments arguments) {
        this.filter = arguments.filter;
        this.dimension = arguments.size;
    }


    private LowerBoundCollapsingDPTupleVariablesMatrixFactory(int dimension, MatrixFilter filter, Matrix C, Map<String, Matrix> lessThanEqC) {
        this.dimension = dimension;
        this.filter = filter;
        this.C = C.add(this.createNullMatrix());
        this.lessThanEqC = new LinkedHashMap<String, Matrix>( lessThanEqC);
    }



    @Override
    public MatrixFactory duplicateSelf() {

        // Warning! If filters get too sophisticated, this as well might raise problems (then duplicateSelf for filters is required)
        // Currently, this is ok.
        return new LowerBoundCollapsingDPTupleVariablesMatrixFactory(this.dimension, this.filter, this.C, this.lessThanEqC);

    }


    @Override
    public boolean supportsArbitraryQDP() {
        return false;
    }

    // TODO: C, all Elements in lessThanEqC belong to the proof!

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
        return this.createOneByOneMatrix(name);
    }

    @Override
    public Matrix createFSymCoefficientMatrix(String name) {
        return this.createColTuple(name).minus(this.createColTuple(name + "-"));
    }

    @Override
    public Matrix createVariableMatrix(String name) {
        if (name.equals(" C")) {
            return this.C;
        }


        VarPolynomial[][] result = new VarPolynomial[this.dimension][1];

        if (this.C == null) {
            this.C = this.createFSymCoefficientMatrix("C_low");
        }

        for (int i = 0; i < this.dimension; i++) {
            result[i][0] = VarPolynomial.createVariable(name + i);
        }
        Matrix LTC = this.createFSymCoefficientMatrix("Var_{" + name + "}");
        this.lessThanEqC .put(name, LTC);
        return new Matrix(result).add(LTC);



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



    private Matrix createRowTuple(String name) {
        VarPolynomial[][] result = new VarPolynomial[1][this.dimension];

        for (int i = 0; i < this.dimension; i++) {

            SimplePolynomial simplePoly = SimplePolynomial.create(name + i);
            result[0][i] = VarPolynomial.create(simplePoly);
            super.addCoefficient(simplePoly);

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
        return this.createRowTuple(name);
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
    public Set<VarPolyConstraint> getExtraConstraints(TermInterpretor ti, Set<FunctionSymbol> Rsignature) {
        if (this.C == null) {
           this.C = this.createFSymCoefficientMatrix("C_low");
        }
        Set<VarPolyConstraint> result = super.getExtraConstraints(ti, Rsignature);
        for (FunctionSymbol f: Rsignature) {
            result.addAll(
                this.getConstraints(
                    ti.interpretTerm(TRSTerm.createFunctionApplication(f, this.generateCList(f.getArity()))),
                    this.C,
                    ConstraintType.GE
                )
            );
        }
        for (Matrix m: this.lessThanEqC.values()) {
            result.addAll(this.getConstraints(this.C, m, ConstraintType.GE));
        }
        return result;
    }

    private ImmutableArrayList<? extends TRSTerm> generateCList(int arity) {
        if (this.cList.containsKey(arity)) {
            return this.cList.get(arity);
        } else {
            ArrayList<TRSTerm> cl = new ArrayList<TRSTerm>();
            for (int i=0; i< arity; i++) {
                cl.add(TRSTerm.createVariable(" C"));
            }
            this.cList.put(arity, ImmutableCreator.create(cl));
            return this.cList.get(arity);
        }
    }

    @Override
    public Set<VarPolyConstraint> getDPConstraints(Matrix interL, Matrix interR) {
        Set<VarPolyConstraint> constraints = new LinkedHashSet<VarPolyConstraint>(this.dimension * this.dimension);
        for (int i = 0; i < interL.getNumRows(); i++) {
            for (int j = 0; j < interR.getNumCols(); j++) {
                constraints.add(new VarPolyConstraint(interL.get(i, j).minus(interR.get(i, j)), ConstraintType.GE));
            }
        }
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
        VarPolynomial[][] result = new VarPolynomial[1][1];

        result[0][0] = VarPolynomial.ZERO;
        return new Matrix(result);
    }

    public int getSize() {
        return this.dimension;
    }

    public MatrixFilter getFilter() {
        return this.filter;
    }

    @Override
    public String proofAddition(Export_Util eu, Map<String, BigInteger> output) {
        StringBuilder res = new StringBuilder();

        res.append("We use lower bounds on ground terms to allow constant part additions to variable interpretations.");
        res.append(eu.newline());
        res.append("Lower bound was " + this.C.specialize(output).toString());
        res.append(eu.newline());
        res.append("Variables have been interpreted as ");
        res.append(eu.newline());
        for (Map.Entry<String, Matrix> e: this.lessThanEqC.entrySet()) {
            res.append(e.getKey());
            res.append(" = indefinite part + ");
            res.append(e.getValue().specialize(output).toString());
            res.append(eu.newline());
        }
        return res.toString();

    }

    public static class Arguments {
        public MatrixFilter filter;
        public int size;
    }

}

