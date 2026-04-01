package aprove.verification.theoremprover.TerminationProcedures;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.TRSProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import immutables.*;

/**
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
@NoParams
public class TRSToQTRSProcessor extends TRSProcessor {

     @Override
    protected Result processProgram(TRS trs, Abortion aborter) throws AbortionException {
         ImmutableSet<Rule> R = ImmutableCreator.create(trs.getProgram().getNewRules());
         boolean innermost = trs.getInnermost();
         Set<TRSFunctionApplication> Q = innermost ? CollectionUtils.getLeftHandSides(R) : new HashSet<TRSFunctionApplication>();

         QTRSProblem qtrs = QTRSProblem.create(R, Q);
         return ResultFactory.proved(qtrs, YNMImplication.EQUIVALENT, new TRSToQTRSProof(Q));
     }

     @Override
    public boolean isEquationalAble() {
         return false;
     }

     private static class TRSToQTRSProof extends Proof {

         private Set<TRSFunctionApplication> Q;

         private TRSToQTRSProof(Set<TRSFunctionApplication> Q) {
             this.Q = Q;
         }


         @Override
        public String export(Export_Util o) {
             StringBuffer s = new StringBuffer();
             s.append(o.export("Transformed TRS into QTRS. Q is:"));
             s.append(o.cond_linebreak());
             s.append(o.set(this.Q, Export_Util.NICE_SET));
             s.append(o.cond_linebreak());
             return s.toString();
         }

     }

}
