package aprove.verification.oldframework.Algebra.PolyMatrices;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * A factory used to create PolyMatrices.
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class PolyMatrixFactory<C extends GPolyCoeff> {

    private final OrderPolyFactory<C> polyFactory;

    private final int dimension;

    // Cache for already built vectors
    private final Map<String, PolyMatrix<C>> variableVectors;

    public PolyMatrixFactory(final OrderPolyFactory<C> polyFactory, final int dimension) {
        this.variableVectors = new HashMap<String, PolyMatrix<C>>();
        this.polyFactory = polyFactory;
        this.dimension = dimension;
    }

    /**
     * Creates a coefficient matrix filled with fresh entries.
     * If collapse is set to true, this coefficient matrix is of
     * size 1xn (line vector), otherwise it is of size nxn (square);
     * here n is the dimension used for the matrices.
     *
     * @param coeffName The basename to use for the entries.
     * @param collapse Collapse square matrix to a line vector?
     */
    public PolyMatrix<C> buildCoeffMatrix(final String coeffName, final boolean collapse) {
        return this.buildCoeffMatrixWithFactor(coeffName, null, collapse);
    }

    /**
     * Creates a coefficient matrix filled with fresh entries.
     * If collapse is set to true, this coefficient matrix is of
     * size 1xn (line vector), otherwise it is of size nxn (square);
     * here n is the dimension used for the matrices.
     *
     * The fresh entries are multiplied by the given factor.
     * Used by arctic matrices below zero for shifting coefficients to >= 0.
     *
     * @param coeffName The basename to use for the entries.
     * @param factor The factor to multiply the variables with;
     *  null if no such factor is desired
     * @param collapse Collapse to a line vector?
     */
    public PolyMatrix<C> buildCoeffMatrixWithFactor(final String coeffName, final C factor, final boolean collapse) {

        if (Globals.useAssertions) {
            assert (coeffName != null);
        }
        final int numberOfRows = collapse ? 1 : this.dimension;
        final List<List<OrderPoly<C>>> entries = new ArrayList<List<OrderPoly<C>>>(this.dimension);
        for (int i = 1; i <= numberOfRows; i++) {
            final List<OrderPoly<C>> row = new ArrayList<OrderPoly<C>>(this.dimension);
            for (int j = 1; j <= this.dimension; j++) {
                final String entryName = coeffName + "#" + ((i - 1) * numberOfRows + j);
                final GPolyVar v = GAtomicVar.createVariable(entryName);
                OrderPoly<C> poly;
                if (factor == null) {
                    poly = this.polyFactory.buildFromInnerVariable(v);
                } else {
                    final VarPartNode<GPolyVar> var = this.polyFactory.buildVariable(v);
                    poly = this.polyFactory.buildFromCoeff(this.polyFactory.getInnerFactory().concat(factor, var));
                }
                row.add(poly);
            }
            entries.add(row);
        }
        return new PolyMatrix<C>(entries);
    }

    /**
     * Creates a coefficient column vector filled with fresh entries.
     *
     * @param coeffName The basename to use for the entries.
     * @param collapse true: build a vector with 1 entry;
     *  false: build a vector with this.dimension entries
     *  (useful for special interpretations for tuple symbols
     *  that collapse to a single number)
     */
    public PolyMatrix<C> buildCoeffVector(final String coeffName, final boolean collapse) {
        return this.buildCoeffVectorWithFactor(coeffName, null, collapse);
    }

    /**
     * Creates a square coefficient column vector filled with fresh entries,
     * which are multiplied by the given factor. Used by arctic matrices
     * below zero for shifting coefficients to >= 0.
     *
     * @param coeffName The basename to use for the entries.
     * @param factor The factor to multiply the variables with;
     *  null if no such factor is desired
     * @param collapse true: build a vector with 1 entry;
     *  false: build a vector with this.dimension entries
     *  (useful for special interpretations for tuple symbols
     *  that collapse to a single number)
     */
    public PolyMatrix<C> buildCoeffVectorWithFactor(final String coeffName, final C factor, final boolean collapse) {

        if (Globals.useAssertions) {
            assert (coeffName != null);
        }
        final int dimension = collapse ? 1 : this.dimension;
        final List<List<OrderPoly<C>>> entries = new ArrayList<List<OrderPoly<C>>>(dimension);
        for (int i = 1; i <= dimension; i++) {
            final List<OrderPoly<C>> row = new ArrayList<OrderPoly<C>>(1);
            final String entryName = coeffName + "#" + i;
            OrderPoly<C> poly;
            final GPolyVar v = GAtomicVar.createVariable(entryName);
            if (factor == null) {
                poly = this.polyFactory.buildFromInnerVariable(v);
            } else {
                final VarPartNode<GPolyVar> var = this.polyFactory.buildVariable(v);
                poly = this.polyFactory.buildFromCoeff(this.polyFactory.getInnerFactory().concat(factor, var));
            }
            row.add(poly);
            entries.add(row);
        }
        return new PolyMatrix<C>(entries);
    }

    /**
     * Creates a variable column vector filled with fresh entries.
     * @param varName The basename to use for the entries.
     * @param exp The exponent of the variable.
     */
    public PolyMatrix<C> buildVariableVector(final String varName) {
        if (this.variableVectors.containsKey(varName)) {
            return this.variableVectors.get(varName);
        }
        final List<List<OrderPoly<C>>> entries = new ArrayList<List<OrderPoly<C>>>(this.dimension);
        for (int i = 1; i <= this.dimension; i++) {
            final List<OrderPoly<C>> row = new ArrayList<OrderPoly<C>>(1);
            final String entryName = varName + "#" + i;
            final OrderPoly<C> varPoly = this.polyFactory.buildFromVariable(GAtomicVar.createVariable(entryName));
            row.add(varPoly);
            entries.add(row);
        }
        final PolyMatrix<C> result = new PolyMatrix<C>(entries);
        this.variableVectors.put(varName, result);
        return result;
    }

    /**
     * Creates a vector (nx1-matrix) that is the product C*x,
     * where C is a square coeff matrix (line vector if
     * collapse is set) with fresh entries
     * and x is a vector of variables.
     * @param coeffName The coefficient's basename.
     * @param varName The variable's basename.
     * @param collapse Collapse to a single polynomial?
     */
    public PolyMatrix<C> buildVarCoeffVector(final String coeffName, final String varName, final boolean collapse) {
        return this.buildVarCoeffVectorWithFactor(coeffName, varName, null, collapse);
    }

    /**
     * Creates a vector that is the product C*x,
     * where C is a coeff line vector with fresh entries
     * and x is a variable.
     * @param coeffName The coefficient's basename.
     * @param varName The variable's basename.
     */
    /*
    public PolyMatrix<C> buildVarCoeff(
            final String coeffName, final String varName) {

        if (Globals.useAssertions) {
            assert(coeffName != null && varName != null);
        }
        List<VarPartNode<GPolyVar>> variables =
            new ArrayList<VarPartNode<GPolyVar>>(this.dimension);
        for (int i = 1; i <= this.dimension; i++) {
            variables.add(this.polyFactory.buildVariable(
                    GAtomicVar.createVariable(varName + "#" + i)));
        }

        List<List<GPoly<C, GPolyVar>>> coeffs =
            new ArrayList<List<GPoly<C, GPolyVar>>>(this.dimension);
        for (int i = 1; i <= this.dimension; i++) {
            List<GPoly<C, GPolyVar>> row =
                new ArrayList<GPoly<C, GPolyVar>>(this.dimension);
            for (int j = 1; j <= this.dimension; j++) {
                String innerVarName = coeffName + "#" + ((i-1) * this.dimension + j);
                GPolyVar innerVar = GAtomicVar.createVariable(innerVarName);
                row.add(this.polyFactory.getInnerFactory().buildFromVariable(innerVar));
            }
            coeffs.add(row);
        }
        List<List<OrderPoly<C>>> entries =
            new ArrayList<List<OrderPoly<C>>>(this.dimension);
        for (int i = 0; i < this.dimension; i++) {
            List<OrderPoly<C>> row = new ArrayList<OrderPoly<C>>(1);
            OrderPoly<C> entry = this.polyFactory.concat(
                    coeffs.get(i).get(0), variables.get(0));
            for (int j = 1; j < this.dimension; j++) {
                 entry = this.polyFactory.plus(entry, this.polyFactory.concat(
                         coeffs.get(i).get(j), variables.get(j)));
            }
            row.add(entry);
            entries.add(row);
        }
        PolyMatrix<C> result = new PolyMatrix<C>(entries);
        return result;
    }
    */

    /**
     * Creates a vector that is the product C*x,
     * where C is a square coeff matrix with fresh entries multiplied
     * by the given factor and x is a vector of variables.
     * Uses by arctic matrices below zero.
     * @param coeffName The coefficient's basename.
     * @param varName The variable's basename.
     * @param factor The factor to multiply the variables with.
     */
    public PolyMatrix<C> buildVarCoeffVectorWithFactor(final String coeffName,
        final String varName,
        final C factor,
        final boolean collapse) {
        if (Globals.useAssertions) {
            assert (coeffName != null && varName != null);
        }

        final int resDim = collapse ? 1 : this.dimension;

        final List<VarPartNode<GPolyVar>> variables = new ArrayList<VarPartNode<GPolyVar>>(this.dimension);
        for (int i = 1; i <= this.dimension; i++) {
            variables.add(this.polyFactory.buildVariable(GAtomicVar.createVariable(varName + "#" + i)));
        }

        final List<List<GPoly<C, GPolyVar>>> coeffs = new ArrayList<List<GPoly<C, GPolyVar>>>(this.dimension);
        for (int i = 1; i <= resDim; i++) {
            final List<GPoly<C, GPolyVar>> row = new ArrayList<GPoly<C, GPolyVar>>(this.dimension);
            for (int j = 1; j <= this.dimension; j++) {
                final String innerVarName = coeffName + "#" + ((i - 1) * resDim + j);
                GPoly<C, GPolyVar> poly;
                final GPolyVar innerV = GAtomicVar.createVariable(innerVarName);
                if (factor == null) {
                    poly = this.polyFactory.getInnerFactory().buildFromVariable(innerV);
                } else {
                    final VarPartNode<GPolyVar> innerVar = this.polyFactory.buildVariable(innerV);
                    poly = this.polyFactory.getInnerFactory().concat(factor, innerVar);
                }
                row.add(poly);
            }
            coeffs.add(row);
        }
        final List<List<OrderPoly<C>>> entries = new ArrayList<List<OrderPoly<C>>>(this.dimension);
        for (int i = 0; i < resDim; i++) {
            final List<OrderPoly<C>> row = new ArrayList<OrderPoly<C>>(1);
            OrderPoly<C> entry = this.polyFactory.concat(coeffs.get(i).get(0), variables.get(0));
            for (int j = 1; j < this.dimension; j++) {
                entry = this.polyFactory.plus(entry, this.polyFactory.concat(coeffs.get(i).get(j), variables.get(j)));
            }
            row.add(entry);
            entries.add(row);
        }
        final PolyMatrix<C> result = new PolyMatrix<C>(entries);
        return result;
    }

    /**
     * Creates a mixed variable column vector filled with fresh entries.
     * @param varNames The basenames to use for the entries.
     */
    /*
    public PolyMatrix<C> buildVariableVector(final Set<String> varNames) {
        if (Globals.useAssertions) {
            assert(varNames.size() > 1);
        }
        List<List<OrderPoly<C>>> entries =
            new ArrayList<List<OrderPoly<C>>>(this.dimension);
        for (int i = 0; i < this.dimension; i++) {
            List<OrderPoly<C>> row = new ArrayList<OrderPoly<C>>(1);
            Set<GPolyVar> variables = new LinkedHashSet<GPolyVar>();
            for (String varName : varNames) {
                String entryName =  varName + "#" + i;
                variables.add(GAtomicVar.createVariable(entryName));
            }
            row.set(i, polyFactory.concat(polyFactory.getCoeffOne(),
                    polyFactory.buildVariables(variables)));
        }
        return new PolyMatrix<C>(entries);
    }
    */

    /*
    public PolyMatrix<C> buildFromVariable(String varName, int cols) {
        return null;
    }
    */

    /**
     * Creates a new matrix as the sum of its arguments.
     * @param leftMatrix
     * @param rightMatrix
     */
    public PolyMatrix<C> plus(final PolyMatrix<C> leftMatrix, final PolyMatrix<C> rightMatrix) {

        final int rows = leftMatrix.numRows();
        final int cols = leftMatrix.numCols();

        if (Globals.useAssertions) {
            assert (cols == rightMatrix.numCols() && rows == rightMatrix.numRows());
        }
        final List<List<OrderPoly<C>>> newEntries = new ArrayList<List<OrderPoly<C>>>(rows);

        for (int i = 0; i < rows; i++) {
            final List<OrderPoly<C>> newRow = new ArrayList<OrderPoly<C>>(cols);
            for (int j = 0; j < cols; j++) {
                newRow.add(this.polyFactory.plus(leftMatrix.at(i, j), rightMatrix.at(i, j)));
            }
            newEntries.add(newRow);
        }
        return new PolyMatrix<C>(newEntries);
    }

    /**
     * Creates a new matrix as the difference of its arguments.
     * @param leftMatrix
     * @param rightMatrix
     */
    public PolyMatrix<C> minus(final PolyMatrix<C> leftMatrix, final PolyMatrix<C> rightMatrix) {

        final int rows = leftMatrix.numRows();
        final int cols = leftMatrix.numCols();

        if (Globals.useAssertions) {
            assert (cols == rightMatrix.numCols() && rows == rightMatrix.numRows());
        }
        final List<List<OrderPoly<C>>> newEntries = new ArrayList<List<OrderPoly<C>>>(rows);
        for (int i = 0; i < rows; i++) {
            final List<OrderPoly<C>> newRow = new ArrayList<OrderPoly<C>>(cols);
            for (int j = 0; j < cols; j++) {
                newRow.add(this.polyFactory.minus(leftMatrix.at(i, j), rightMatrix.at(i, j)));
            }
            newEntries.add(newRow);
        }
        return new PolyMatrix<C>(newEntries);
    }

    /**
     * Creates a new matrix as the matrix product of its arguments.
     * @param leftMatrix
     * @param rightMatrix
     */
    public PolyMatrix<C> multiply(final PolyMatrix<C> leftMatrix, final PolyMatrix<C> rightMatrix) {

        final int leftRows = leftMatrix.numRows();
        final int rightRows = rightMatrix.numRows();
        final int leftCols = leftMatrix.numCols();
        final int rightCols = rightMatrix.numCols();

        if (Globals.useAssertions) {
            assert (rightRows == leftCols);
        }

        final List<List<OrderPoly<C>>> newElements = new ArrayList<List<OrderPoly<C>>>(leftRows);
        for (int i = 0; i < leftRows; i++) {
            final List<OrderPoly<C>> newRow = new ArrayList<OrderPoly<C>>(rightCols);
            for (int j = 0; j < rightCols; j++) {
                OrderPoly<C> newEntry = this.polyFactory.times(leftMatrix.at(i, 0), rightMatrix.at(j, 0));
                for (int k = 1; k < leftCols; k++) {
                    newEntry =
                        this.polyFactory.plus(newEntry,
                            this.polyFactory.times(leftMatrix.at(i, k), rightMatrix.at(j, k)));
                }
                newRow.add(newEntry);
            }
            newElements.add(newRow);
        }
        return new PolyMatrix<C>(newElements);
    }

    /**
     * Perform variable substitution on all entries of a matrix.
     * @param matrix The matrix.
     * @param substitution The substitution.
     * @return The resulting matrix.
     */
    public PolyMatrix<C> substituteVariables(final PolyMatrix<C> matrix,
        final Map<GPolyVar, GPoly<GPoly<C, GPolyVar>, GPolyVar>> substitution,
        final Abortion aborter) throws AbortionException {
        final List<List<OrderPoly<C>>> newEntries = new ArrayList<List<OrderPoly<C>>>(matrix.numRows());
        for (int i = 0; i < matrix.numRows(); i++) {
            final List<OrderPoly<C>> newRow = new ArrayList<OrderPoly<C>>(matrix.numCols());
            for (int j = 0; j < matrix.numCols(); j++) {
                aborter.checkAbortion();
                newRow.add(this.polyFactory.substituteVariables(matrix.at(i, j), substitution, null, aborter));
            }
            newEntries.add(newRow);
        }
        return new PolyMatrix<C>(newEntries);
    }
}
