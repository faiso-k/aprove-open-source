package aprove.verification.oldframework.Algebra.Matrices;

import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * Represents a single Matrix constraint (>=, = or >)
 * @author Patrick Kabasci
 * @version $Id$
 */
public class MatrixConstraint {

    private Matrix left, right;
    private MatrixFactory fact;
    private ConstraintType type;

    public MatrixConstraint(Matrix left, Matrix right, MatrixFactory fact, ConstraintType type) {
        this.left = left;
        this.right = right;
        this.fact = fact;
        this.type = type;
    }

    public Collection<? extends VarPolyConstraint> getVPCs() {
        return this.fact.getConstraints(this.left, this.right, this.type);
    }


}

