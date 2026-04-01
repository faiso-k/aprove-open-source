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

public class PlainMatrixDioCreator {

    /* result is <dio const for satisfying ct, null> if ct <> GT or autostrict = false
     *           <dio const for satisfying >=, additional dio const for satisfying >> if ct = GE and autostrict = true
     */
    public Pair<Set<Diophantine>, Diophantine> getDio(MatrixParamTerm mpt, ConstraintType ct, boolean autostrict) {
        Set<Diophantine> res1 = new LinkedHashSet<Diophantine>();
        Diophantine res2 = null;

        for (TRSVariable v : mpt.getVariables()) {
            SimpleMatrix sm = mpt.getCoefficient(v);
            if (ct.equals(ConstraintType.EQ)) {
                res1.addAll(this.getDio(sm, ConstraintType.EQ));
            } else {
                res1.addAll(this.getDio(sm, ConstraintType.GE));
            }
        }

        res1.addAll(this.getDio(mpt.getConstant(), ct));
        if (autostrict && ct.equals(ConstraintType.GE)) {
            res2 = this.getAutostrict(mpt.getConstant(), ConstraintType.GT);
        }

        return new Pair<Set<Diophantine>, Diophantine>(res1, res2);
    }

    private Set<Diophantine> getDio(SimpleMatrix sm, ConstraintType ct) {
        Set<Diophantine> res = new LinkedHashSet<Diophantine>();
        int dimX = sm.dimX();
        int dimY = sm.dimY();
        for (int x = 0; x < dimX; x++) {
            for (int y = 0; y < dimY; y++) {
                res.add(Diophantine.create(sm.get(x, y), ct));
            }
        }
        return res;
    }

    private Diophantine getAutostrict(SimpleMatrix sm, ConstraintType ct) {
        return Diophantine.create(sm.get(0, 0), ct);
    }

}
