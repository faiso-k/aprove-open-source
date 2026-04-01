package aprove.verification.dpframework.PADPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.SMT_LIA.SMTLIB.*;
import aprove.verification.dpframework.PADPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Removes dependency pairs with an unsatisfiable constraint.
 *
 * @author Stephan Falke
 * @version $Id$
 */
@NoParams
public class PADPUnsatProcessor extends PADPProcessor {

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.PADPProblem.Processors.PADPUnsatProcessor");

    @Override
    protected Result processPADP(PADPProblem padp, Abortion aborter) throws AbortionException {
        List<PARule> p = new Vector<PARule>(padp.getP());
        List<Set<PAConstraint>> cs = new Vector<Set<PAConstraint>>();

        for (PARule dp : p) {
            cs.add(dp.getConstraint());
        }

        List<String> liac = new Vector<String>();

        for (Set<PAConstraint> css : cs) {
            liac.add(PAConstraint.toSMTLIB(css));
        }

        Set<PARule> delP = new LinkedHashSet<PARule>();
        Set<PARule> newP = new LinkedHashSet<PARule>();

        for (PARule dp : p) {
            if (!dp.getConstraint().isEmpty()) {
                final YNM sat = YicesChecker.callYices(liac.get(0), PADPUnsatProcessor.log, aborter);
                if (sat == YNM.NO) {
                    delP.add(dp);
                } else {
                    newP.add(dp);
                }
            } else {
                newP.add(dp);
            }
            String dummy = liac.remove(0);
        }

        if (delP.isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        Proof proof = new PADPUnsatProof(delP);
        PADPProblem newPADP = PADPProblem.create(ImmutableCreator.create(newP), padp.getPATRS(), padp.getDefTup());
        return ResultFactory.proved(newPADP, YNMImplication.EQUIVALENT, proof);
    }

    private static class PADPUnsatProof extends Proof.DefaultProof {

        private Set<PARule> deletedPairs;

        private PADPUnsatProof(Set<PARule> deletedPairs) {
            this.deletedPairs = deletedPairs;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("The following dependency pairs are removed because they have an unsatisfiable constraint:");
            result.append(o.cond_linebreak());
            result.append(o.set(this.deletedPairs, Export_Util.RULES));
            result.append(o.cond_linebreak());
            return result.toString();
        }
    }

}
