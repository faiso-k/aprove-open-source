package aprove.verification.complexity.LowerBounds.Util.Transformations;

import java.util.*;

import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;


public class TermToSumOfPolynomials {

    private TermToPolynomial arithExpTransformer;
    private TrsTypes types;

    public TermToSumOfPolynomials(TrsTypes types) {
        this.types = types;
        this.arithExpTransformer = new TermToPolynomial(types);
    }

    public SimplePolynomial transform(TRSFunctionApplication t) {
        SimplePolynomial res = SimplePolynomial.ZERO;
        List<TRSTerm> args = t.getArguments();
        List<Type> argTypes = this.types.get(t.getRootSymbol()).getArgumentTypes();
        for (int i = 0; i < argTypes.size(); i++) {
            TRSTerm arg = args.get(i);
            if (argTypes.get(i).equals(Type.Nats)) {
                res = res.plus(this.arithExpTransformer.transform(arg));
            } else if (arg instanceof TRSFunctionApplication){
                res = res.plus(this.transform((TRSFunctionApplication)arg));
            }
        }
        return res;
    }

}
