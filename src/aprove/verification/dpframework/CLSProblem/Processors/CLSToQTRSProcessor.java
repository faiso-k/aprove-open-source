package aprove.verification.dpframework.CLSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CLSProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.dpframework.TRSProblem.Processors.CTRSToQTRSProcessor.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

@NoParams
public class CLSToQTRSProcessor extends CLSProcessor {

    @Override
    public boolean isCLSApplicable(final CLSProblem obl) {
        return true;
    }

    @Override
    protected Result processCLS(final CLSProblem problem, final Abortion aborter) throws AbortionException {
        final CTRSProblem ctrs = CLSToCTRSProcessor.CLSToCTRS(problem);
        final FreshNameGenerator fg = ctrs.getFreshNameGenerator();
        final Map<ConditionalRule, List<Rule>> mapping = new HashMap<>();
        final Set<Rule> newRules = CTRSToQTRSProcessor.translate(ctrs.getC(), fg, true, true, mapping);
        newRules.addAll(ctrs.getR());
        final QTermSet Q = new QTermSet(CollectionUtils.getLeftHandSides(newRules));
        final QTRSProblem qtrs = QTRSProblem.create(ImmutableCreator.create(newRules),Q);
        final Proof proof = new CTRSToQTRSProof(ctrs, mapping);
        return ResultFactory.proved(qtrs, YNMImplication.SOUND, new CLSToQTRSProof(proof));
    }

    public class CLSToQTRSProof extends DefaultProof {

        private final Proof proof;

        public CLSToQTRSProof(final Proof proof) {
            this.proof = proof;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Sliced variables and converted to unconditional TRS:"+o.linebreak()+this.proof.export(o);
        }

    }

}
