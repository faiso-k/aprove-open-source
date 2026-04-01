package aprove.verification.dpframework.CSDPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

@NoParams
public class QCSUsableRulesProcessor extends QCSDPProcessor {

    @Override
    public boolean isQCSDPApplicable(QCSDPProblem obl) {
        return true;
    }

    @Override
    public Result processQCSDP(QCSDPProblem problem, Abortion aborter)
            throws AbortionException {
        aborter.checkAbortion();
        ImmutableSet<Rule> r = problem.getRInPrefixForm(TRSTerm.STANDARD_PREFIX);

        QCSUsableRules ur = problem.getQCSUsableRules();

        Set<Rule> usable = ur.estimatedCSUsableRules(problem.getDp());

        Set<Rule> unusable = new LinkedHashSet<Rule>(r);
        unusable.removeAll (usable);

        if (Globals.useAssertions) {
            for (Rule l_to_r : usable) {
                assert (r.contains(l_to_r));
            }
        }

        if (unusable.isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        QCSDPProblem todo = QCSDPProblem.create(problem, ImmutableCreator
                .create(usable));

        Proof proof = new QCSUsableRulesProof(unusable);

        return ResultFactory.proved(todo, YNMImplication.EQUIVALENT, proof);
    }

    private class QCSUsableRulesProof extends Proof.DefaultProof {

        private final Set<Rule> unusable;

        public QCSUsableRulesProof(Set<Rule> unusable) {
            this.unusable = unusable;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();

            s.append("The following rules are not useable "
                    + o.cite(Citation.DA_EMMES) + " and can be deleted:"
                    + o.cond_linebreak());
            s.append(o.set(this.unusable, Export_Util.RULES));

            return s.toString();
        }
    }
}
