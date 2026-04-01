package aprove.verification.dpframework.PATRSProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.SMT_LIA.SMTLIB.*;
import aprove.verification.dpframework.PATRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Removes rewrite rules with an unsatisfiable constraint.
 *
 * @author Stephan Falke
 * @version $Id$
 */
@NoParams
public class PATRSUnsatProcessor extends PATRSProcessor {

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.PATRSProblem.Processors.PATRSUnsatProcessor");

    @Override
    protected Result processPATRS(PATRSProblem patrs, Abortion aborter) throws AbortionException {
        List<PARule> r = new Vector<PARule>(patrs.getR());
        List<Set<PAConstraint>> cs = new Vector<Set<PAConstraint>>();

        for (PARule rule : r) {
            cs.add(rule.getConstraint());
        }

        List<String> liac = new Vector<String>();

        for (Set<PAConstraint> css : cs) {
            liac.add(PAConstraint.toSMTLIB(css));
        }

        Set<PARule> delR = new LinkedHashSet<PARule>();
        Set<PARule> newR = new LinkedHashSet<PARule>();

        for (PARule rule : r) {
            if (!rule.getConstraint().isEmpty()) {
                final YNM sat = YicesChecker.callYices(liac.get(0), PATRSUnsatProcessor.log, aborter);
                if (sat == YNM.NO) {
                    delR.add(rule);
                } else {
                    newR.add(rule);
                }
            } else {
                newR.add(rule);
            }
            String dummy = liac.remove(0);
        }

        if (delR.isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        ImmutableSet<PARule> newRi = ImmutableCreator.create(newR);
        Proof proof = new PATRSUnsatProof(patrs, delR);
        PATRSProblem newPATRS = PATRSProblem.create(newRi, patrs.getS(), patrs.getE(), patrs.getSortMap());
        return ResultFactory.proved(newPATRS, YNMImplication.EQUIVALENT, proof);
    }

    private static class PATRSUnsatProof extends Proof.DefaultProof {

        private PATRSProblem PATRS;
        private Set<PARule> deletedRules;

        private PATRSUnsatProof(PATRSProblem PATRS, Set<PARule> deletedRules) {
            this.PATRS = PATRS;
            this.deletedRules = deletedRules;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("The following rules are removed because they have an unsatisfiable constraint:");
            result.append(o.cond_linebreak());
            result.append(o.set(this.deletedRules, Export_Util.RULES));
            result.append(o.cond_linebreak());
            return result.toString();
        }
    }

}
