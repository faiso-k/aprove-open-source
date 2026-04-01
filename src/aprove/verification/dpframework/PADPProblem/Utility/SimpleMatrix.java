package aprove.verification.dpframework.PADPProblem.Utility;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * Matrix of SimplePolynomial.
 *
 * @author Stephan Falke
 * @version $Id$
 */

public class SimpleMatrix implements Exportable {

    private final int hashCode;
    private SimplePolynomial[][] theMatrix;
    private int dimX;
    private int dimY;

    private SimpleMatrix(int dimX, int dimY, BigInteger defaultEntry) {
        this.dimX = dimX;
        this.dimY = dimY;
        this.theMatrix = new SimplePolynomial[dimX][dimY];
        for (int x = 0; x < dimX; x++) {
            for (int y = 0; y < dimY; y++) {
                this.theMatrix[x][y] = SimplePolynomial.create(defaultEntry);
            }
        }
        this.hashCode = this.dimX * 3 + this.dimY * 7757;
    }

    public static SimpleMatrix create(int dimX, int dimY, BigInteger defaultEntry) {
        return new SimpleMatrix(dimX, dimY, defaultEntry);
    }

    /**
     * Deprecation due to BigInteger probably being more suitable for PATRS
     * than Integer as seen from the underlying theory (PATRSs work on Z,
     * not on bitvectors of length 32); maybe drop deprecation, though,
     * since (+1)^{2^31} is not "likely" to occur in many input files.
     * @deprecated
     */
    @Deprecated
    public static SimpleMatrix create(int dimX, int dimY, int defaultEntry) {
        return new SimpleMatrix(dimX, dimY, BigInteger.valueOf(defaultEntry));
    }

    public static SimpleMatrix create(List<String> coeff) {
        int dim = coeff.size();
        SimpleMatrix res = SimpleMatrix.create(1, dim, BigInteger.ZERO);
        for (int i = 0; i < dim; i++) {
            res.theMatrix[0][i] = SimplePolynomial.create(coeff.get(i));
        }
        return res;
    }

    public static SimpleMatrix createFull(List<List<String>> coeffs) {
        int dimY = coeffs.size();
        int dimX = coeffs.get(0).size();
        SimpleMatrix res = SimpleMatrix.create(dimX, dimY, BigInteger.ZERO);
        for (int x = 0; x < dimX; x++) {
            for (int y = 0; y < dimY; y++) {
                res.theMatrix[x][y] = SimplePolynomial.create(coeffs.get(y).get(x));
            }
        }
        return res;
    }

    public static SimpleMatrix createUnit(int dim) {
        SimpleMatrix res = SimpleMatrix.create(dim, dim, BigInteger.ZERO);
        for (int i = 0; i < dim; i++) {
            res.theMatrix[i][i] = SimplePolynomial.create(1);
        }
        return res;
    }

    public static SimpleMatrix createDiagonal(int dim, int value) {
        SimpleMatrix res = SimpleMatrix.create(dim, dim, BigInteger.ZERO);
        for (int i = 0; i < dim; i++) {
            res.theMatrix[i][i] = SimplePolynomial.create(value);
        }
        return res;
    }

    public void set(int x, int y, SimplePolynomial value) {
        this.theMatrix[x][y] = value;
    }

    public SimplePolynomial get(int x, int y) {
        return this.theMatrix[x][y];
    }

    public int dimX() {
        return this.dimX;
    }

    public int dimY() {
        return this.dimY;
    }

    /** Adds a SimpleMatrix of same size.
     */
    public SimpleMatrix plus(SimpleMatrix sm) {
        if (sm.dimX != this.dimX || sm.dimY != this.dimY) {
            throw new RuntimeException("Incompatible sizes in SimpleMatrix.plus");
        }
        SimpleMatrix res = new SimpleMatrix(this.dimX, this.dimY, BigInteger.ZERO);
        for (int x = 0; x < this.dimX; x++) {
            for (int y = 0; y < this.dimY; y++) {
                res.theMatrix[x][y] = this.get(x, y).plus(sm.get(x, y));
            }
        }
        return res;
    }

    /** Subtracts a SimpleMatrix of same size.
     */
    public SimpleMatrix minus(SimpleMatrix sm) {
        if (sm.dimX != this.dimX || sm.dimY != this.dimY) {
            throw new RuntimeException("Incompatible sizes in SimpleMatrix.minus");
        }
        return this.plus(sm.negate());
    }

    /** Negates a SimpleMatrix.
     */
    public SimpleMatrix negate() {
        SimpleMatrix res = new SimpleMatrix(this.dimX, this.dimY, BigInteger.ZERO);
        for (int x = 0; x < this.dimX; x++) {
            for (int y = 0; y < this.dimY; y++) {
                res.theMatrix[x][y] = this.get(x, y).negate();
            }
        }
        return res;
    }

    /** Multiplies a SimpleMatrix from the right.
     */
    public SimpleMatrix times(SimpleMatrix sm) {
        if (sm.dimY != this.dimX) {
            throw new RuntimeException("Incompatible sizes in SimpleMatrix.times");
        }
        SimpleMatrix res = new SimpleMatrix(sm.dimX, this.dimY, BigInteger.ZERO);
        for (int y = 0; y < this.dimY; y++) {
            for (int x = 0; x < sm.dimX; x++) {
                res.theMatrix[x][y] = this.mult(y, sm, x);
            }
        }
        return res;
    }

    private SimplePolynomial mult(int y, SimpleMatrix sm, int x) {
        SimplePolynomial res = SimplePolynomial.create(0);
        for (int i = 0; i < this.dimX; i++) {
            res = res.plus(this.get(i, y).times(sm.get(x, i)));
        }
        return res;
    }

    public SimpleMatrix specialize(Map<String, BigInteger> values) {
        SimpleMatrix res = new SimpleMatrix(this.dimX, this.dimY, BigInteger.ZERO);
        for (int x = 0; x < this.dimX; x++) {
            for (int y = 0; y < this.dimY; y++) {
                res.theMatrix[x][y] = this.get(x, y).specialize(values);
            }
        }
        return res;
    }

    // "Stolen" from PolyMatrix.
    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder();

        if (o instanceof PLAIN_Util) {
            // special treatment for plain export
            sb.append("[");
            for (int i = 0; i < this.dimY; i++) {
                if (i > 0) {
                    sb.append (", ");
                }
                sb.append("[");
                for (int j = 0; j < this.dimX; j++) {
                    if (j > 0) {
                        sb.append (", ");
                    }
                    sb.append(this.get(j, i).export(o));
                }
                sb.append("]");
            }
            sb.append("]");
            return sb.toString();
        }

        if (this.dimY == 1) {
            if (this.dimX == 1) {
                // just a number
                sb.append(o.math(this.get(0, 0).export(o)));
            } else {
                // line vector
                List<String> rowEntries = new ArrayList<String>(this.dimX + 2);
                rowEntries.add(o.math("["));
                for (int i = 0; i < this.dimX; i++) {
                    SimplePolynomial sp = this.get(0, i);
                    if (i != this.dimX - 1) {
                        rowEntries.add(o.math(sp.export(o) + ","));
                    } else {
                        rowEntries.add(o.math(sp.export(o)));
                    }
                }
                rowEntries.add(o.math("]"));
                sb.append(o.tableStart(rowEntries.size()));
                sb.append(o.tableRow(rowEntries));
                sb.append(o.tableEnd());
            }
        } else {
            // at least 2 rows
            List<String> rowEntries = new ArrayList<String>(this.dimX + 2);

            // row 1
            rowEntries.add(o.math("/"));
            for (int x = 0; x < this.dimX; x++) {
                SimplePolynomial sp = this.get(x, 0);
                rowEntries.add(o.math(sp.export(o)));
            }
            rowEntries.add(o.math(o.escape("\\")));
            sb.append(o.tableStart(rowEntries.size()));
            sb.append(o.tableRow(rowEntries));
            rowEntries.clear();

            // inner rows
            final int lastRow = this.dimY - 1;
            for (int i = 1; i < lastRow; i++) {
                rowEntries.add(o.math("|"));
                for (int x = 0; x < this.dimX; x++) {
                    SimplePolynomial sp = this.get(x, i);
                    rowEntries.add(o.math(sp.export(o)));
                }
                rowEntries.add(o.math("|"));
                sb.append(o.tableRow(rowEntries));
                rowEntries.clear();
            }

            // last row
            rowEntries.add(o.math(o.escape("\\")));
            for (int x = 0; x < this.dimX; x++) {
                SimplePolynomial sp = this.get(x, lastRow);
                rowEntries.add(o.math(sp.export(o)));
            }
            rowEntries.add(o.math("/"));
            sb.append(o.tableRow(rowEntries));
            sb.append(o.tableEnd());
        }

        return sb.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    @Override
    public boolean equals(Object oth) {
        if (this == oth) {
            return true;
        }
        if (oth == null) {
            return false;
        }
        if (oth.getClass() != this.getClass()) {
            return false;
        }
        SimpleMatrix other = (SimpleMatrix) oth;
        if (this.dimX != other.dimX || this.dimY != other.dimY) {
            return false;
        }
        for (int x = 0; x < this.dimX; x++) {
            for (int y = 0; y < this.dimY; y++) {
                if (!this.get(x, y).equals(other.get(x, y))) {
                    return false;
                }
            }
        }
        return true;
    }

}
