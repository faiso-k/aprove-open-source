package aprove.verification.oldframework.Algebra.Matrices;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Represents n by n matrices over VarPolynomials over Z.
 *
 * Also provides methods for common matrix operations, i.e.
 * - multiplication
 * - transposition
 * - addition
 *
 * Note that a number is- in certain situations-
 * a 1x1 matrix
 * and a (Column/Row)-n-tuple a nx1 or 1xn matrix.
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public class Matrix implements Immutable, Exportable {

    private final static Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Matrices.Matrix");

    private final VarPolynomial[][] coefficients;

    /**
     * Construct a matrix given the mentioned elements.
     *
     * Performs a deep copy of the given array.
     * @param entries
     */
    public static Matrix create(final VarPolynomial[][] entries) {
        VarPolynomial[][] coefficients;
        if (entries.length >= 1) {
            coefficients = new VarPolynomial[entries.length][entries[0].length];
            final int lenX = entries.length;
            final int lenY = entries[0].length;
            for (int i=0; i<lenX; i++) {
                if (Globals.useAssertions) {
                    assert(lenY == entries[i].length);
                }
                for (int j=0; j<lenY; j++) {
                    coefficients[i][j] = entries[i][j];
                }
            }
            return new Matrix(coefficients);
        } else {
            if (Globals.useAssertions) {
                assert false;
            }
            return null;
        }
    }

    /**
     * For package internal use:
     * Construct a matrix *using* the mentioned array
     */
    Matrix(final VarPolynomial[][] entries) {
        this.coefficients = entries;
    }


    /**
     * Return a matrix entry.
     *
     * @param i The row of the element to be returned.
     * @param j The column of the element to be returned.
     * @return The requested element.
     */
    public VarPolynomial get(final int i, final int j) {
        return this.coefficients[i][j];
    }


    /**
     * Transpose the matrix.
     */
    public Matrix transpose() {
        VarPolynomial[][] transposedEntries;
        transposedEntries = new VarPolynomial[this.coefficients[0].length][this.coefficients.length];
        final int lenX = this.coefficients.length;
        final int lenY = this.coefficients[0].length;
        for (int i=0; i<lenX; i++) {
            if (Globals.useAssertions) {
                assert(lenY == this.coefficients[i].length);
            }
            for (int j=0; j<lenY; j++) {
                transposedEntries[j][i] = this.coefficients[i][j];
            }
        }
        return new Matrix(transposedEntries);
    }


    /**
     * Substract two matrices: this matrix and the specified matrix.
     * Return a new matrix consisting of the difference of the two.
     */
    public Matrix minus(final Matrix other) {
        // Assert that both matrixes are compatible
        if (Globals.useAssertions) {
            assert (other.coefficients.length == this.coefficients.length);
            assert (other.coefficients[0].length == this.coefficients[0].length);
        }
        VarPolynomial[][] sumCoeffs;
        sumCoeffs = new VarPolynomial[other.coefficients.length][other.coefficients[0].length];

        final int lenX = this.coefficients.length;
        final int lenY = this.coefficients[0].length;
        for (int i=0; i<lenX; i++) {
            for (int j=0; j<lenY; j++) {
                sumCoeffs[i][j] = this.coefficients[i][j].minus(other.coefficients[i][j]);
            }
        }
        final Matrix diff = new Matrix(sumCoeffs);
        return diff;
    }


    /**
     * Add two matrices: this matrix and the specified matrix.
     * Return a new matrix consisting of the sum of the two.
     */
    public Matrix add(final Matrix other) {
        // Assert that both matrixes are compatible
        if (Globals.useAssertions) {
            assert (other.coefficients.length == this.coefficients.length);
            assert (other.coefficients[0].length == this.coefficients[0].length);
        }
        VarPolynomial[][] sumCoeffs;
        sumCoeffs = new VarPolynomial[other.coefficients.length][other.coefficients[0].length];

        final int lenX = this.coefficients.length;
        final int lenY = this.coefficients[0].length;
        for (int i=0; i<lenX; i++) {
            for (int j=0; j<lenY; j++) {
                sumCoeffs[i][j] = this.coefficients[i][j].plus(other.coefficients[i][j]);
            }
        }
        final Matrix sum = new Matrix(sumCoeffs);
        return sum;
    }



    /**
     * Add several matrices.
     * Return a new matrix consisting of the sum of the two.
     */
    public static Matrix add(final List<Matrix> args) {
        int dimX = 0;
        int dimY = 0;

        List<VarPolynomial>[][] addends = new List[0][0];

        for (final Matrix arg: args) {
            if (dimX == 0) {
                dimX = arg.getNumRows();
                dimY = arg.getNumCols();
                addends = new List[dimX][dimY];
            }
            if (Globals.useAssertions) {
                assert dimX == arg.getNumRows();
                assert dimY == arg.getNumCols();
            }
            for (int i=0; i<dimX; i++) {
                for (int j=0; j<dimY; j++) {
                    if (addends[i][j] == null) {
                        addends[i][j] = new ArrayList<VarPolynomial> ();
                    }
                    addends[i][j].add(arg.coefficients[i][j]);
                }
            }
        }
        final VarPolynomial[][] result = new VarPolynomial[dimX][dimY];

        for (int i=0; i<dimX; i++) {
            for (int j=0; j<dimY; j++) {
                result[i][j] = VarPolynomial.plus(addends[i][j]);
            }
        }

        return new Matrix(result);

    }

    /**
     * Multiply other matrix from the right
     * i.e. a.multiplyRight(b) = a.b
     *
     * @param other
     * @return Product
     */
    public Matrix multiplyRight(final Matrix other) {

        // Assert that both matrixes are compatible
        if (Globals.useAssertions) {
            assert (this.coefficients[0].length == other.coefficients.length);
        }

        final List<VarPolynomial> addends = new ArrayList<VarPolynomial> ();
        final int interleaveSize = other.coefficients.length;
        final int sizeY = this.coefficients.length;
        final int sizeX = other.coefficients[0].length;
        final VarPolynomial[][] prodCoeffs = new VarPolynomial[sizeY][sizeX];
        for (int i=0; i < sizeY; i++) {
            for (int j=0; j < sizeX; j++) {
                addends.clear();
                for (int k=0; k < interleaveSize; k++ ) {
                     addends.add (this.coefficients[i][k].times(other.coefficients[k][j]));
                }
                prodCoeffs[i][j] = VarPolynomial.plus(addends);
            }
        }
        return new Matrix(prodCoeffs);
    }

    /**
     * Multiplies a scalar a to the Matrix M as in a*M.
     * @param scalar The scalar to multiply with
     * @return
     */
    public Matrix multiplyScalar(final SimplePolynomial scalar) {
        final int sizeY = this.coefficients.length;
        final int sizeX = this.coefficients[0].length;
        final VarPolynomial[][] prodCoeffs = new VarPolynomial[sizeY][sizeX];
        for (int i=0; i < sizeY; i++) {
            for (int j=0; j < sizeX; j++) {
                prodCoeffs[i][j] = this.get(i,j).times(scalar);
            }
        }
        return new Matrix(prodCoeffs);
    }

    /**
     * Multiply other sqared matrices of the same size (!) from the right to this matrix
     * i.e. a.multiplyRight([b,c]) = a.b.c
     *
     * We do not check that all matrices are of the same size, however we assume that!
     *
     * @param other
     * @return Product
     */
    public Matrix multiplyRight(final Matrix[] other) {

        long timer, ntimer =0;

        final List<VarPolynomial> addends = new ArrayList<VarPolynomial> ();


        final int interleaveSize = this.coefficients.length;
        final int sizeY = this.coefficients.length;
        final int sizeX = this.coefficients[0].length;
        final VarPolynomial[][] prodCoeffs = new VarPolynomial[sizeY][sizeX];
        final VarPolynomial[][] coefficients = new VarPolynomial[sizeY][sizeX];

        for(int i=0; i< sizeY; i++) {
            for (int j=0; j< sizeX; j++) {
                coefficients[i][j] = this.coefficients[i][j];
            }
        }
        for (final Matrix m: other) {
            for (int i=0; i < sizeY; i++) {
                for (int j=0; j < sizeX; j++) {
                    addends.clear();
                    for (int k=0; k < interleaveSize; k++ ) {
                        timer = System.currentTimeMillis();
                        addends.add (coefficients[i][k].times(m.coefficients[k][j]));
                        ntimer += System.currentTimeMillis() - timer;
                    }
                    prodCoeffs[i][j] = VarPolynomial.plus(addends);
                }
            }
            for(int i=0; i< sizeY; i++) {
                for (int j=0; j< sizeX; j++) {
                    coefficients[i][j] = prodCoeffs[i][j];
                }
            }
        }
        Matrix.log.log(Level.FINEST, "Cummulative VarPoly multiplication took " + Long.toString(ntimer) + "ms\n");
        return new Matrix(prodCoeffs);
    }

    /**
     * Multiply other matrix from the left
     * i.e. a.multiplyRight(b) = b.a
     *
     * @param other
     * @return
     */
    public Matrix multiplyLeft(final Matrix other) {
        return other.multiplyRight(this);
    }

    /**
     * @return the number of Rows of that matrix
     */
    public int getNumRows() {
        return this.coefficients.length;
    }

    /**
     * @return the number of Columns of that matrix
     */
    public int getNumCols() {
        return this.coefficients[0].length;
    }

    /**
     *
     * @param mapping A mapping from the matrix' coefficients (denoted "name_i,j") to their value
     * @return The matrix with all coefficients specialized.
     */
    public Matrix specialize(final Map<String, BigInteger> mapping) {
        final VarPolynomial[][] result = new VarPolynomial[this.getNumRows()][this.getNumCols()];
        for (int i=0; i < this.getNumRows(); i++) {
            for (int j=0; j < this.getNumCols(); j++) {
                result[i][j] = this.coefficients[i][j].specialize(mapping);
            }
        }
        return new Matrix(result);
    }

    /* Note that this is intentionally not "Compareable", as
     * e.g.   / 1 0 \               / 0 0 \
     *        \ 0 0 /        and    \ 1 0 /
     *        are not compareable at all; the order is thus partial.
     */

    /**
     * Checks whether this matrix is strictly greater than the other
     * matrix, where strictly greater than <=> one component is
     * strictly greater than and the others are >=.
     * @param other
     * @return
     */
    public boolean isGT(final Matrix other) {
        // Check compatibility.
        if (Globals.useAssertions) {
            assert this.getNumCols() == other.getNumCols();
            assert this.getNumRows() == other.getNumRows();
        }
        boolean foundStrict = false;
        for (int i=0; i < this.getNumRows(); i++) {
            for (int j=0; j < this.getNumCols(); j++) {
                final VarPolynomial diff = this.coefficients[i][j].minus(other.get(i,j));
                VarPolyConstraint constr = new VarPolyConstraint(diff, ConstraintType.GE);
                if (!constr.isValid()) {
                    return false;
                }
                constr = new VarPolyConstraint(diff, ConstraintType.GT);
                foundStrict |= constr.isValid();
            }
        }
        return foundStrict;
    }

    /**
     * Checks whether this matrix is >= than the other
     * matrix, where >= <=> all components are >=.
     * @param other
     * @return
     */
    public boolean isGE(final Matrix other) {
        // Check compatibility.
        if (Globals.useAssertions) {
            assert this.getNumCols() == other.getNumCols();
            assert this.getNumRows() == other.getNumRows();
        }
        for (int i=0; i < this.getNumRows(); i++) {
            for (int j=0; j < this.getNumCols(); j++) {
                final VarPolynomial diff = this.coefficients[i][j].minus(other.get(i,j));
                final VarPolyConstraint constr = new VarPolyConstraint(diff, ConstraintType.GE);
                if (!constr.isValid()) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * @return a matrix in which all indefinite coeffs have been replaced by 0
     */
    public Matrix setAllIndefsToZero() {
        VarPolynomial[][] result;
        result = new VarPolynomial[this.coefficients.length][this.coefficients[0].length];

        final int lenX = this.coefficients.length;
        final int lenY = this.coefficients[0].length;
        for (int i=0; i<lenX; i++) {
            for (int j=0; j<lenY; j++) {
                result[i][j] = this.coefficients[i][j].specialize(new DefaultValueMap<String, BigInteger>(BigInteger.ZERO));
            }
        }
        return new Matrix(result);
    }



    /**
     * It's not cute, but it works.
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append("[");
        for (int i=0; i<this.getNumRows(); i++) {
            if (i>0) {
                sb.append (", ");
            }
            sb.append("[");
            for (int j=0; j<this.getNumCols(); j++) {
                if (j>0) {
                    sb.append (", ");
                }
                sb.append(this.coefficients[i][j].toString());
            }
            sb.append("]");
        }
        sb.append("]");
        return sb.toString();
    }

    public Element toRatCPF(final Document doc, final int denominator, final int dimension) {
        final Element matrix = CPFTag.MATRIX.create(doc);
        for (int j = 0; j < dimension; j++) {
            final Element mvect = CPFTag.VECTOR.create(doc);
            for (int i = 0; i < dimension; i++) {
                final Element e =
                    j < this.getNumCols() && i < this.getNumRows()
                        ? this.get(i, j).toRatCPF(doc, denominator)
                            : CPFTag.COEFFICIENT.create(doc, CPFTag.INTEGER.create(doc, 0));
                mvect.appendChild(e);
            }
            matrix.appendChild(mvect);
        }
        return matrix;
    }

    @Override
    public String export(final Export_Util o) {
        if (o instanceof PLAIN_Util) {
            return this.toString();
        }
        final StringBuilder sb = new StringBuilder();
        if (this.getNumRows() == 1) {
            if (this.getNumCols() == 1) {
                // just a number
                sb.append(o.math(this.get(0, 0).export(o)));
            }
            else {
                // line vector
                final List<String> rowEntries = new ArrayList<String>(this.getNumCols() + 2);
                rowEntries.add(o.math("["));
                for (int i = 0; i < this.coefficients[0].length; ++i) {
                    final VarPolynomial vp = this.coefficients[0][i];
                    if (i != this.coefficients[0].length - 1) {
                        rowEntries.add(o.math(vp.export(o)+","));
                    }
                    else {
                        rowEntries.add(o.math(vp.export(o)));
                    }
                }
                rowEntries.add(o.math("]"));
                sb.append(o.tableStart(rowEntries.size()));
                sb.append(o.tableRow(rowEntries));
                sb.append(o.tableEnd());
            }
        }
        else {
            // at least 2 rows
            final List<String> rowEntries = new ArrayList<String>(this.getNumCols() + 2);

            // row 1
            rowEntries.add(o.math("/"));
            for (final VarPolynomial vp : this.coefficients[0]) {
                rowEntries.add(o.math(vp.export(o)));
            }
            rowEntries.add(o.math(o.escape("\\")));
            sb.append(o.tableStart(rowEntries.size()));
            sb.append(o.tableRow(rowEntries));
            rowEntries.clear();

            // inner rows
            for (int i = 1; i < this.getNumRows() - 1; ++i) {
                rowEntries.add(o.math("|"));
                for (final VarPolynomial vp : this.coefficients[i]) {
                    rowEntries.add(o.math(vp.export(o)));
                }
                rowEntries.add(o.math("|"));
                sb.append(o.tableRow(rowEntries));
                rowEntries.clear();
            }

            // last row
            rowEntries.add(o.math(o.escape("\\")));
            for (final VarPolynomial vp : this.coefficients[this.getNumRows() - 1]) {
                rowEntries.add(o.math(vp.export(o)));
            }
            rowEntries.add(o.math("/"));
            sb.append(o.tableRow(rowEntries));
            sb.append(o.tableEnd());
        }
        return sb.toString();
    }



    public Matrix getCol(final int i) {

        final VarPolynomial[][] retCol = new VarPolynomial[this.getNumRows()][1];
        for (int j=0; j< this.getNumRows(); j++) {
          retCol[j][0] = this.coefficients[j][i];
        }

        return new Matrix(retCol);

    }

    /**
     * getList returns a List of all non-zero entries of this matrix.
     * @return
     */
    public List<VarPolynomial> getList() {
        final List<VarPolynomial> ret = new ArrayList<VarPolynomial>
          (this.coefficients.length * (this.coefficients.length > 0? this.coefficients[0].length: 0));
        for (int i=0; i < this.coefficients.length; i++) {
            for (int j=0; j < this.coefficients[0].length; j++) {
                if (! this.coefficients[i][j].equals(VarPolynomial.ZERO)) {
                    ret.add (this.coefficients[i][j]);
                }
            }
        }
        return ret;
    }
    
    /**
     * getList returns a List of all entries of this matrix.
     * @return
     */
    public List<VarPolynomial> getCompleteList() {
        final List<VarPolynomial> ret = new ArrayList<VarPolynomial>(this.coefficients.length * this.coefficients[0].length);
        for (int i=0; i < this.coefficients.length; i++) {
            for (int j=0; j < this.coefficients[0].length; j++) {
                ret.add (this.coefficients[i][j]);
                
            }
        }
        return ret;
    }


    /**
     * Creates a skelleton matrix for this matrix, i.e. a matrix of the form ax + b
     * if this matrix is of the form (complex simplepolynomial)x + (complex simplepolynomial)
     * @param name The coefficient name for this skelleton
     * @param ranges The map of ranges to be used
     * @param defaultRange The default range to be used
     * @return
     */
    public Matrix createSkelleton(final String name, final Map<String, BigIntegerInterval> ranges) {
        final VarPolynomial[][] result = new VarPolynomial[this.getNumRows()][this.getNumCols()];
        for (int i=0; i < this.getNumRows(); i++) {
            for (int j=0; j < this.getNumCols(); j++) {
                result[i][j] = this.coefficients[i][j].getSkelleton(name + "_" + i + "," + j, ranges);
            }
        }
        return new Matrix(result);

    }

    public Matrix dupColumns(final int cols) {
        final VarPolynomial[][] tmp = new VarPolynomial[this.coefficients.length][this.coefficients[0].length * cols];
        for (int i=0; i< this.coefficients.length; i++) {

            for (int j = 0; j < cols; j++) {
                for (int k=0; k< this.coefficients[0].length; k++) {
                    tmp[i][j*this.coefficients[0].length+k] = this.coefficients[i][k];
                }
            }

        }

        return new Matrix(tmp);
    }

    public Matrix dupColumnsInterleaved(final int cols) {
        final VarPolynomial[][] tmp = new VarPolynomial[this.coefficients.length][this.coefficients[0].length * cols];
        for (int i=0; i< this.coefficients.length; i++) {

            for (int k=0; k< this.coefficients[0].length; k++) {
                for (int j = 0; j < cols; j++) {
                    tmp[i][k*cols+j] = this.coefficients[i][k];
                }
            }

        }

        return new Matrix(tmp);
    }


    public boolean isGround() {
        for (int i=0; i< this.getNumCols(); i++) {
            for (int j=0; j< this.getNumRows(); j++) {
                if (!this.coefficients[j][i].isConstant()) {
                    return false;
                }
            }
        }
        return true;
    }

}

