package aprove.verification.dpframework.PADPProblem.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

public class PlainDioCreator {

    /* result is <dio const for satisfying ct, null> if ct <> GT or autostrict = false
     *           <dio const for satisfying >=, additional dio const for satisfying >> if ct = GE and autostrict = true
     */
    public Pair<Set<Diophantine>, Diophantine> getDio(LinearParamTerm lpt, ConstraintType ct, boolean autostrict) {
        Set<Diophantine> res1 = new LinkedHashSet<Diophantine>();
        Diophantine res2 = null;

        for (TRSVariable v : lpt.getVariables()) {
            SimplePolynomial sp = lpt.getCoefficient(v);
            if (ct.equals(ConstraintType.EQ)) {
                res1.add(Diophantine.create(sp, ConstraintType.EQ));
            } else {
                res1.add(Diophantine.create(sp, ConstraintType.GE));
            }
        }

        res1.add(Diophantine.create(lpt.getConstant(), ct));
        if (autostrict && ct.equals(ConstraintType.GE)) {
            res2 = Diophantine.create(lpt.getConstant(), ConstraintType.GT);
        }

        return new Pair<Set<Diophantine>, Diophantine>(res1, res2);
    }

}
