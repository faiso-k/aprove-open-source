package aprove.verification.dpframework.PATRSProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.PATRSProblem.*;
import aprove.verification.dpframework.PATRSProblem.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Removes rewrite rules where lhs is reducible by S.
 *
 * @author Stephan Falke
 * @version $Id$
 */
@NoParams
public class PATRSReducibleProcessor extends PATRSProcessor {

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.PATRSProblem.Processors.PATRSReducibleProcessor");

    @Override
    protected Result processPATRS(PATRSProblem patrs, Abortion aborter) throws AbortionException {
        List<PARule> r = new Vector<PARule>(patrs.getR());
        Map<FunctionSymbol, Set<Rule>> smap = Rule.getRuleMap(patrs.getS());
        Set<Equation> e = patrs.getE();

        Set<PARule> delR = new LinkedHashSet<PARule>();
        Set<PARule> newR = new LinkedHashSet<PARule>();

        for (PARule rule : r) {
            if (this.isReducible(rule.getLeft(), smap, e)) {
                delR.add(rule);
            } else {
                newR.add(rule);
            }
        }

        if (delR.isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        ImmutableSet<PARule> newRi = ImmutableCreator.create(newR);
        Proof proof = new PATRSReducibleProof(patrs, delR);
        PATRSProblem newPATRS = PATRSProblem.create(newRi, patrs.getS(), patrs.getE(), patrs.getSortMap());
        return ResultFactory.proved(newPATRS, YNMImplication.EQUIVALENT, proof);
    }

    private boolean isReducible(TRSTerm t, Map<FunctionSymbol, Set<Rule>> smap, Set<Equation> e) {
        Set<TRSTerm> tclass = EquivalenceClassGenerator.getEquivalenceClass(t, e);

        for (TRSTerm s : tclass) {
            if (!s.rewrite(smap).isEmpty()) {
                return true;
            }
        }

        return false;
    }

    private static class PATRSReducibleProof extends Proof.DefaultProof {

        private PATRSProblem PATRS;
        private Set<PARule> deletedRules;

        private PATRSReducibleProof(PATRSProblem PATRS, Set<PARule> deletedRules) {
            this.PATRS = PATRS;
            this.deletedRules = deletedRules;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("The following rules are removed because their left-hand side is reducible by S:");
            result.append(o.cond_linebreak());
            result.append(o.set(this.deletedRules, Export_Util.RULES));
            result.append(o.cond_linebreak());
            return result.toString();
        }
    }

}
