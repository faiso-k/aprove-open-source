package aprove.verification.oldframework.Algebra.Polynomials;

import java.util.*;

/**
 *
 * This class builds VarPolynomials without generating several immutable
 * intermediate results.
 * A VarPolynomialBuilder is not immutable; don't store it anywhere!
 * However it can be flattened and will yield an immutable VarPolynomial.
 * It is specially optimized for multiplying complex polynomials with
 * simple ones as happens frequently in matrix interpretations.
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public class VarPolynomialBuilder {

    // 1 - add
    // 2 - multiply
    private int type;

    private List<VarPolynomialBuilder> varPolyBuilderOperands;
    private List<IndefinitePart> coeffOperands;
    private List<IndefinitePart> variableOperands;
    private List<VarPolynomial> varPolyOperands;




}

