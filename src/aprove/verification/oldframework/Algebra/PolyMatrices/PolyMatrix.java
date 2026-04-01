package aprove.verification.oldframework.Algebra.PolyMatrices;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;
import aprove.xml.*;

/**
 * Represents nxm-matrices over OrderPolys.
 *
 * @param C The type of the polynomials' coefficients.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class PolyMatrix<C extends GPolyCoeff> implements GPolyCoeff, XMLObligationExportable {

    private List<List<OrderPoly<C>>> entries;
    private final int rows, cols;

    public PolyMatrix(final List<List<OrderPoly<C>>> entries) {
        this.entries = entries;
        this.cols = entries.get(0).size();
        this.rows = entries.size();
    }

    /**
     * Alias for get().
     */
    public OrderPoly<C> at(final int row, final int col) {
        return this.get(row, col);
    }

    /**
     * Get a specific matrix entry.
     *
     * @param row
     * @param col
     * @return this[row, col]
     */
    public OrderPoly<C> get(final int row, final int col) {
        if (Globals.useAssertions) {
            assert(row <= this.rows && col <= this.cols);
        }
        return this.entries.get(row).get(col);
    }


    /**
     * @return the number of rows in the matrix
     */
    public int numRows() {
        return this.rows;
    }

    /**
     * @return the number of columns in the matrix
     */
    public int numCols() {
        return this.cols;
    }

    /**
     * Apply the given visitor to all entries of the matrix.
     * @param v Some GPolyVisitor for outer polynomials.
     */
    public void visit(final GPolyVisitor<GPoly<C, GPolyVar>, GPolyVar> v) {

        if (Globals.useAssertions) {
           assert(v != null);
        }
        final List<List<OrderPoly<C>>> newEntries = new ArrayList<List<OrderPoly<C>>>(this.rows);
        for (final List<OrderPoly<C>> row : this.entries) {
            final List<OrderPoly<C>> newRow = new ArrayList<OrderPoly<C>>(this.cols);
            for (final OrderPoly<C> entry : row) {
                final OrderPoly<C> newEntry = new OrderPoly<C>(v.applyTo(entry));
                newRow.add(newEntry);
            }
            newEntries.add(newRow);
        }
        this.entries = newEntries;
    }

    /**
     * Flatten the entries of the matrix.
     * @param fvOuter A FlatteningVisitor for the outer polys.
     * @param fvInner A FlatteningVisitor for the inner polys. If null,
     * only the outer polys are flattened.
     */
    public void flatten(
            final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter,
            final FlatteningVisitor<C, GPolyVar> fvInner,
            final OrderPolyFactory<C> factory) {

        if (Globals.useAssertions) {
            assert(fvOuter != null);
        }
        this.visit(fvOuter);
        if (fvInner != null) {
            final Semiring<GPoly<C, GPolyVar>> polyRing = fvOuter.getRingC();
            final CMonoid<GMonomial<GPolyVar>> monoid = fvInner.getMonoid();
            final List<List<OrderPoly<C>>> newEntries =
                new ArrayList<List<OrderPoly<C>>>(this.rows);
            for (final List<OrderPoly<C>> row : this.entries) {
                final List<OrderPoly<C>> newRow = new ArrayList<OrderPoly<C>>(this.cols);
                for (final OrderPoly<C> entry : row) {
                    final Map<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> monomials =
                        entry.getMonomials(polyRing, monoid);
                    final Set<GPoly<GPoly<C, GPolyVar>, GPolyVar>> newMonomials =
                        new LinkedHashSet<GPoly<GPoly<C, GPolyVar>, GPolyVar>>(monomials.size());
                    for (final Map.Entry<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> monomial
                            : monomials.entrySet()) {
                        final GPoly<C, GPolyVar> coeff = monomial.getValue();
                        newMonomials.add(factory.concat(coeff.visit(fvInner),
                                VarPartNode.fromMonomial(monomial.getKey())));
                    }
                    newRow.add(new OrderPoly<C>(
                            factory.getFactory().plus(newMonomials)));
                }
                newEntries.add(newRow);
            }
            this.entries = newEntries;
        }
    }

    /**
     * Returns a string representation of the matrix without "beautifying"
     * the contained polynomials. Warning: Ugly. Use exportFlat() instead.
     */
    @Override
    public String export(final Export_Util o) {
        if (o instanceof PLAIN_Util) {
            // special treatment for plain export
            final StringBuilder sb = new StringBuilder();
            sb.append("[");
            for (int i = 0; i < this.rows; i++) {
                if (i > 0) {
                    sb.append (", ");
                }
                sb.append("[");
                final List<OrderPoly<C>> currentRow = this.entries.get(i);
                for (int j = 0; j < this.cols; j++) {
                    if (j > 0) {
                        sb.append (", ");
                    }
                    sb.append(currentRow.get(j).export(o));
                }
                sb.append("]");
            }
            sb.append("]");
            return sb.toString();
        }

        final StringBuilder sb = new StringBuilder();
        if (this.numRows() == 1) {
            if (this.numCols() == 1) {
                // just a number
                sb.append(o.math(this.get(0, 0).export(o)));
            }
            else {
                // line vector
                final List<String> rowEntries = new ArrayList<String>(this.numCols() + 2);
                rowEntries.add(o.math("["));
                final int length = this.entries.get(0).size();
                for (int i = 0; i < length; ++i) {
                    final OrderPoly<C> vp = this.get(0, i);
                    if (i != length - 1) {
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
            final List<String> rowEntries = new ArrayList<String>(this.numCols() + 2);

            // row 1
            rowEntries.add(o.math("/"));
            for (final OrderPoly<C> vp : this.entries.get(0)) {
                rowEntries.add(o.math(vp.export(o)));
            }
            rowEntries.add(o.math(o.escape("\\")));
            sb.append(o.tableStart(rowEntries.size()));
            sb.append(o.tableRow(rowEntries));
            rowEntries.clear();

            // inner rows
            final int lastRow = this.numRows() - 1;
            for (int i = 1; i < lastRow; ++i) {
                rowEntries.add(o.math("|"));
                for (final OrderPoly<C> vp : this.entries.get(i)) {
                    rowEntries.add(o.math(vp.export(o)));
                }
                rowEntries.add(o.math("|"));
                sb.append(o.tableRow(rowEntries));
                rowEntries.clear();
            }

            // last row
            rowEntries.add(o.math(o.escape("\\")));
            for (final OrderPoly<C> vp : this.entries.get(lastRow)) {
                rowEntries.add(o.math(vp.export(o)));
            }
            rowEntries.add(o.math("/"));
            sb.append(o.tableRow(rowEntries));
            sb.append(o.tableEnd());
        }
        return sb.toString();
    }

    /**
     * Returns a string representation of the matrix after flattening the contained
     * polynomials.
     * @param inner A FlatteningVisitor for the inner polynomials.
     * @param outer A FlatteningVisitor for the outer polynomials.
     * @param o the Export_Util to use.
     */
    public String exportFlat(
            final FlatteningVisitor<C, GPolyVar> inner,
            final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> outer,
            final Export_Util o) {
        final StringBuilder sb = new StringBuilder();
        if (this.numRows() == 1) {
            if (this.numCols() == 1) {
                // just a number
                sb.append(o.math(this.get(0, 0).exportFlatDeep(inner, outer, o)));
            }
            else {
                // line vector
                final List<String> rowEntries = new ArrayList<String>(this.numCols() + 2);
                rowEntries.add(o.math("["));
                final int length = this.entries.get(0).size();
                for (int i = 0; i < length; ++i) {
                    final OrderPoly<C> vp = this.get(0, i);
                    if (i != length - 1) {
                        rowEntries.add(o.math(vp.exportFlatDeep(inner, outer, o)+","));
                    }
                    else {
                        rowEntries.add(o.math(vp.exportFlatDeep(inner, outer, o)));
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
            final List<String> rowEntries = new ArrayList<String>(this.numCols() + 2);

            // row 1
            rowEntries.add(o.math("/"));
            for (final OrderPoly<C> vp : this.entries.get(0)) {
                rowEntries.add(o.math(vp.exportFlatDeep(inner, outer, o)));
            }
            rowEntries.add(o.math(o.escape("\\")));
            sb.append(o.tableStart(rowEntries.size()));
            sb.append(o.tableRow(rowEntries));
            rowEntries.clear();

            // inner rows
            final int lastRow = this.numRows() - 1;
            for (int i = 1; i < lastRow; ++i) {
                rowEntries.add(o.math("|"));
                for (final OrderPoly<C> vp : this.entries.get(i)) {
                    rowEntries.add(o.math(vp.exportFlatDeep(inner, outer, o)));
                }
                rowEntries.add(o.math("|"));
                sb.append(o.tableRow(rowEntries));
                rowEntries.clear();
            }

            // last row
            rowEntries.add(o.math(o.escape("\\")));
            for (final OrderPoly<C> vp : this.entries.get(lastRow)) {
                rowEntries.add(o.math(vp.exportFlatDeep(inner, outer, o)));
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
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {

        final Element matrixTag = XMLTag.MATRIX.createElement(doc);
        if (this.cols < 2) {
            final Element vectorTag = XMLTag.MVECT.createElement(doc);
            for (int row = 0; row < this.rows; row++) {
                final OrderPoly<C> entryPoly = this.entries.get(row).get(0);
                final List<C> coeffs = entryPoly.getInnerPoly().getCoeffs();
                if (Globals.useAssertions) {
                    assert(coeffs.size() > 0);
                }
                final C entry = coeffs.get(0);
                if (entry instanceof XMLObligationExportable) {
                    vectorTag.appendChild(((XMLObligationExportable) entry).toDOM(doc, xmlMetaData));
                }
            }
            matrixTag.appendChild(vectorTag);
        } else {
            for (int col = 0; col < this.cols; col++) {
                final Element vectorTag = XMLTag.MVECT.createElement(doc);
                for (int row = 0; row < this.rows; row++) {
                    // Wherever XML export matters, we want to see matrices of numbers
                    // and not of polynomials.
                    final OrderPoly<C> entryPoly = this.entries.get(row).get(col);
                    final List<C> coeffs = entryPoly.getInnerPoly().getCoeffs();
                    if (Globals.useAssertions) {
                        assert(coeffs.size() > 0);
                    }
                    final C entry = coeffs.get(0);
                    if (entry instanceof XMLObligationExportable) {
                        vectorTag.appendChild(((XMLObligationExportable) entry).toDOM(doc, xmlMetaData));
                    }
                }
                matrixTag.appendChild(vectorTag);
            }
        }
        return matrixTag;
    }

    /**
     * a field for storing the dimension of the original matrix for filling the vector if necessary
     * this is only for toCPF method use
     */
    private int dimension = 1;

    /**
     * set the dimension for using in export
     * @param dimension to be set
     */
    public void setDimension(final int dimension) {
        this.dimension = dimension;
    }

    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData, final boolean arctic) {
        final Element polynomial = CPFTag.POLYNOMIAL.createElement(doc);
        final Element coefficient = CPFTag.COEFFICIENT.createElement(doc);
        if (this.cols < 2) {
            final Element vectorTag = CPFTag.VECTOR.createElement(doc);
            for (int row = 0; row < this.rows; row++) {
                final OrderPoly<C> entryPoly = this.entries.get(row).get(0);
                final List<C> coeffs = entryPoly.getInnerPoly().getCoeffs();
                if (Globals.useAssertions) {
                    assert (coeffs.size() > 0);
                }
                final C entry = coeffs.get(0);
                if (entry instanceof CPFAdditional) {
                    final Element vectorCoefficient = CPFTag.COEFFICIENT.createElement(doc);
                    vectorCoefficient.appendChild(((CPFAdditional) entry).toCPF(doc, xmlMetaData));
                    vectorTag.appendChild(vectorCoefficient);
                }
            }
            for (int filling = 0; (this.rows + filling) < this.dimension; filling++) {
                vectorTag.appendChild(CPFTag.COEFFICIENT.create(doc, arctic
                    ? CPFTag.MINUS_INFINITY.create(doc)
                        : CPFTag.INTEGER.create(doc, doc.createTextNode("0"))));
            }
            coefficient.appendChild(vectorTag);
        } else {
            final Element matrix = CPFTag.MATRIX.createElement(doc);
            for (int col = 0; col < this.cols; col++) {
                final Element vectorTag = CPFTag.VECTOR.createElement(doc);
                for (int row = 0; row < this.rows; row++) {
                    // Wherever XML export matters, we want to see matrices of numbers
                    // and not of polynomials.
                    final OrderPoly<C> entryPoly = this.entries.get(row).get(col);
                    final List<C> coeffs = entryPoly.getInnerPoly().getCoeffs();
                    if (Globals.useAssertions) {
                        assert (coeffs.size() > 0);
                    }
                    final C entry = coeffs.get(0);
                    if (entry instanceof CPFAdditional) {
                        final Element vectorCoefficient = CPFTag.COEFFICIENT.createElement(doc);
                        vectorCoefficient.appendChild(((CPFAdditional) entry).toCPF(doc, xmlMetaData));
                        vectorTag.appendChild(vectorCoefficient);
                    }
                }
                for (int filling = 0; (this.rows + filling) < this.dimension; filling++) {
                    vectorTag.appendChild(CPFTag.COEFFICIENT.create(doc, arctic
                        ? CPFTag.MINUS_INFINITY.create(doc)
                            : CPFTag.INTEGER.create(doc, doc.createTextNode("0"))));
                }
                matrix.appendChild(vectorTag);
            }
            coefficient.appendChild(matrix);
        }
        polynomial.appendChild(coefficient);
        return polynomial;
    }

}
