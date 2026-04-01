package aprove.verification.theoremprover.Simplifier;

import java.util.logging.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.theoremprover.TerminationProofs.*;

public abstract class SimplifierProcessor extends Processor.ProcessorSkeleton {

    public String pName;
    public String psName;
    public String plName;
    public String msg;
    public Proof proof;

    protected static Logger log = Logger.getLogger("aprove.verification.theoremprover.TerminationProcedures.Processor");

    public SimplifierProcessor(String pName,String psName,String plName) {
        this.pName = pName;
        this.psName = psName;
        this.plName = plName;
        // removing all spaces, since this is to be used as Name in the Strategy
        this.pName = this.pName.replaceAll(" ","");
    }

    public void setMessage(String msg){
        this.msg = msg;
    }

    public void setProof(Proof proof){
        this.proof = proof;
    }

    public abstract SimplifierObligation simplify(SimplifierObligation obl) throws AbortionException;

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {

        aborter.checkAbortion();

        SimplifierProblem simpl = (SimplifierProblem)obl;
        SimplifierObligation sObl = simpl.getSimplifierObligation();
        this.proof = null;
        SimplifierObligation newSObl = this.simplify(sObl);
        if (newSObl != null) {
            SimplifierProblem newSimpl = new SimplifierProblem(simpl.getName(NameLength.SHORT), simpl.getName(NameLength.LONG), newSObl);
            if (this.proof != null) {
                return ResultFactory.proved(newSimpl, YNMImplication.EQUIVALENT, this.proof);
            }
            else {
                return ResultFactory.proved(newSimpl, YNMImplication.EQUIVALENT, new SimplifierProof(sObl, newSObl, this.pName, this.psName, this.plName, this.msg));
            }
        }
        else {
            return ResultFactory.unsuccessful();
        }
    }


    @Override
    public boolean isApplicable(BasicObligation o) {
        return (o instanceof SimplifierProblem);
    }

}
