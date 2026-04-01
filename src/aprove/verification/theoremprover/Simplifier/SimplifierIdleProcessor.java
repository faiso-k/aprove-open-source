package aprove.verification.theoremprover.Simplifier;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

@NoParams
public abstract class SimplifierIdleProcessor extends SimplifierProcessor{

    public SimplifierIdleProcessor(String pName,String psName,String plName) {
        super(pName,psName,plName);
    }

    protected Result process(SimplifierObligation input) throws AbortionException {
        SimplifierObligation obl = input;
        SimplifierObligation robl = this.simplify(obl);
        if (robl != null) {
            return ResultFactory.proved(new SimplifierProof(obl,robl,this.pName,this.psName,this.plName,this.msg));
        } else {
            return ResultFactory.unsuccessful();
        }
    }

}
