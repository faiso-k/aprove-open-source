package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials;

import org.w3c.dom.*;

import aprove.xml.*;

/**
 * An OpApp has the form max(p1, p2) or min(p1, p2) where p1 and p2 are
 * OpVarPolynomials (i.e., polynomial expressions augmented by max and min
 * of such expressions).
 *
 * @author fuhs
 * @version $Id$
 */
public class OpApp implements XMLObligationExportable {

    private final boolean isMax;
    private final OpVarPolynomial leftArg;
    private final OpVarPolynomial rightArg;

    private OpApp(final boolean isMax, final OpVarPolynomial leftArg, final OpVarPolynomial rightArg) {
        this.isMax = isMax;
        this.leftArg = leftArg;
        this.rightArg = rightArg;
    }

    /**
     * @param leftArg
     * @param rightArg
     * @return max(leftArg, rightArg)
     */
    public static OpApp createMax(final OpVarPolynomial leftArg, final OpVarPolynomial rightArg) {
        return new OpApp(true, leftArg, rightArg);
    }

    /**
     * @param leftArg
     * @param rightArg
     * @return min(leftArg, rightArg)
     */
    public static OpApp createMin(final OpVarPolynomial leftArg, final OpVarPolynomial rightArg) {
        return new OpApp(false, leftArg, rightArg);
    }

    /**
     * Creates a new OpApp of the same type as this.
     */
    public OpApp createWithNewArgs(final OpVarPolynomial leftArg, final OpVarPolynomial rightArg) {
        return new OpApp(this.isMax, leftArg, rightArg);
    }

    /**
     * @return true, if this is max(leftArg, rightArg);
     *  false, if this is min(leftArg, rightArg)
     */
    public boolean isMax() {
        return this.isMax;
    }

    /**
     * @return the leftArg
     */
    public OpVarPolynomial getLeftArg() {
        return this.leftArg;
    }

    /**
     * @return the rightArg
     */
    public OpVarPolynomial getRightArg() {
        return this.rightArg;
    }

    @Override
    public String toString() {
        return (this.isMax ? "max(" : "min(") + this.leftArg + ", "
                                              + this.rightArg + ")";
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {

        Element appTag;
        if (this.isMax) {
            appTag = XMLTag.MAX.createElement(doc);
        } else {
            appTag = XMLTag.MIN.createElement(doc);
        }
        appTag.appendChild(this.leftArg.toDOM(doc, xmlMetaData));
        appTag.appendChild(this.rightArg.toDOM(doc, xmlMetaData));
        return appTag;
    }

}
