package aprove.verification.oldframework.IntTRS.LinearRedPair;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Algebra.Matrices.*;
import aprove.verification.oldframework.BasicStructures.*;


/**
 * A LCS (Linear Constraint System) is a set of linear constraints.
 * These are stored in the form of
 * (A;A') (x,x') =< b
 * where ';' (',') denotes row-by-row (column-by-column) concatenation.
 * Additionally we store the original rule.
 *
 * @author Matthias Hoelzel
 *
 */
public class LCS implements Exportable {
    /**
     * The first matrix, representing the old values.
     */
    private final Matrix matrixA;

    /**
     * The second matrix, representing the new values.
     */
    private final Matrix matrixAPrime;

    /**
     * The vector, that finalizes the constraints.
     */
    private final Matrix vectorb;

    /** Origin rule */
    private final IGeneralizedRule origin;

    /**
     * It is a beautiful constructor. (Don't complain!)
     * @param matA the first matrix
     * @param matAPrime the second matrix
     * @param vecb the vector b (here it is a matrix too)
     * @param originalRule the original rule
     */
    public LCS(final Matrix matA, final Matrix matAPrime, final Matrix vecb,
               final IGeneralizedRule originalRule) {
        this.matrixA = matA;
        this.matrixAPrime = matAPrime;
        this.vectorb = vecb;
        this.origin = originalRule;
    }

    /**
     * Getter for A.
     * @return Matrix
     */
    public Matrix getA() {
        return this.matrixA;
    }

    /**
     * Getter for A'.
     * @return Matrix
     */
    public Matrix getAPrime() {
        return this.matrixAPrime;
    }

    /**
     * Getter for b.
     * @return a vector in form of a matrix
     */
    public Matrix getb() {
        return this.vectorb;
    }

    /**
     * Getter for leftSymbol.
     * @return FunctionSymbol
     */
    public FunctionSymbol getLeftSymbol() {
        return this.origin.getLeft().getRootSymbol();
    }

    /**
     * Returns the rule where this LCS comes from.
     * @return IGeneralizedRule
     */
    public IGeneralizedRule getOriginRule() {
        return this.origin;
    }

    /**
     * Getter for rightSymbol.
     * @return FunctionSymbol
     */
    public FunctionSymbol getRightSymbol() {
        return ((TRSFunctionApplication) this.origin.getRight()).getRootSymbol();
    }

    @Override
    public String toString() {
        String result;

        result = "LCS:\nA  = " + this.matrixA;
        result += "\nA' = " + this.matrixAPrime;
        result += "\nb  = " + this.vectorb;
        result += "\nLeft symbol = " + this.getLeftSymbol()
                + " Right symbol = " + this.getRightSymbol();
        result += "\n";

        return result;
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder sb = new StringBuilder();
        sb.append(this.getLeftSymbol().export(eu));
        sb.append(eu.escape("("));
        sb.append(eu.fontcolor(eu.escape("x") + eu.sup(eu.escape("T")), Color.RED));
        sb.append(eu.escape(")"));

        sb.append(eu.rightarrow());

        sb.append(this.getRightSymbol().export(eu));
        sb.append(eu.escape("("));
        sb.append(eu.fontcolor(eu.escape("y") + eu.sup(eu.escape("T")), Color.RED));
        sb.append(eu.escape(")"));
        sb.append(eu.escape(", "));
        sb.append(eu.fontcolor("if ", Color.GREEN));

        sb.append(eu.fontcolor(eu.escape("A"), Color.BLUE));
        sb.append(eu.multSign());
        sb.append(eu.fontcolor(eu.escape("x"), Color.RED));
        sb.append(eu.escape(" + "));
        sb.append(eu.fontcolor(eu.escape("A'"), Color.BLUE));
        sb.append(eu.multSign());
        sb.append(eu.fontcolor(eu.escape("y"), Color.RED));
        sb.append(eu.leSign());
        sb.append(eu.fontcolor(eu.escape("b"), Color.BLUE));

        sb.append(eu.fontcolor(eu.escape(" where"), Color.GREEN));
        sb.append(eu.linebreak());

        sb.append(eu.fontcolor(eu.escape("A "), Color.BLUE));
        sb.append(eu.eqSign());
        sb.append(this.matrixA.export(eu));
        sb.append(eu.linebreak());

        sb.append(eu.fontcolor(eu.escape("A' "), Color.BLUE));
        sb.append(eu.eqSign());
        sb.append(this.matrixAPrime.export(eu));
        sb.append(eu.linebreak());

        sb.append(eu.fontcolor(eu.escape("b "), Color.BLUE));
        sb.append(eu.eqSign());
        sb.append(this.vectorb.export(eu));
        sb.append(eu.linebreak());

        return sb.toString();
    }

}
