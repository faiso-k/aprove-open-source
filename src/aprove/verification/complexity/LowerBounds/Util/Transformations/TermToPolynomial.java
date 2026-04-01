package aprove.verification.complexity.LowerBounds.Util.Transformations;

import java.util.*;

import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Used to transform a term that represents an arithmetic expression to a polynomial.
 */
public class TermToPolynomial {

    private Set<TRSFunctionApplication> constants = new LinkedHashSet<>();
    private TrsTypes types;

    public TermToPolynomial(TrsTypes types) {
        this.types = types;
    }

    public SimplePolynomial transform(TRSTerm arithmExp) {
        assert PFHelper.isArithExp(arithmExp);
        if (PFHelper.isInt(arithmExp)) {
            return SimplePolynomial.create(PFHelper.toInt(arithmExp));
        }
        if (arithmExp.isVariable() || (types != null && PFHelper.isUnknownIntConstant(arithmExp, this.types))) {
            if (arithmExp.isConstant()) {
                this.constants.add((TRSFunctionApplication) arithmExp);
            }
            return SimplePolynomial.create(arithmExp.getName());
        }
        SimplePolynomial res = this.transform((TRSFunctionApplication) arithmExp);
        if (res == null && types == null && arithmExp.isConstant()) {
            this.constants.add((TRSFunctionApplication) arithmExp);
            return SimplePolynomial.create(arithmExp.getName());
        } else {
            return res;
        }
    }

    private SimplePolynomial transform(TRSFunctionApplication arithmExp) {
        FunctionSymbol symbol = arithmExp.getRootSymbol();
        if (symbol.getArity() == 0) {
            return null;
        }
        SimplePolynomial arg1 = this.transform(arithmExp.getSubterm(Position.create(0)));
        if (arg1 == null) {
            return null;
        }
        if (symbol.getArity() != 2) {
            return null;
        }
        SimplePolynomial arg2 = this.transform(arithmExp.getSubterm(Position.create(1)));
        if (arg2 == null) {
            return null;
        }
        if (symbol == PFHelper.ADD) {
            return arg1.plus(arg2);
        } else if (symbol == PFHelper.MUL) {
            return arg1.times(arg2);
        } else {
            return null;
        }
    }

    public Set<TRSFunctionApplication> getConstants() {
        return this.constants;
    }

}
