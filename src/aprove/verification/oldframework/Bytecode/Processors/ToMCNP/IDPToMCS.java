package aprove.verification.oldframework.Bytecode.Processors.ToMCNP;

// THIS IS NOT FINISHED YET! //


import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.Processors.*;
import aprove.verification.dpframework.MCSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Matthias Hoelzel
 */
public class IDPToMCS extends IDPProcessor {
    /**
     * Constructor
     */
    public IDPToMCS() {
        super();
    }

    /**
     * @return true IFF this processor will accept the given obligation.
     * @param idp a IDPProblem
     */
    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        // for now require to be at least as restrictive as innermost
        // and at most the domains of Integers (and Booleans)
        final Set<Domain> allowedDomains = new LinkedHashSet<Domain>();
        allowedDomains.add(DomainFactory.INTEGERS);
        allowedDomains.add(DomainFactory.BOOLEAN);
        return idp.getRuleAnalysis().isNfQSubsetEqNfR()
          && allowedDomains.containsAll(idp.getRuleAnalysis().getDomains());
    }

    /**
     * Work on the given obligation.
     *
     * @param obl an IDPProblem.
     * @param abortion ignored.
     * @throws AbortionException can be aborted
     * @return some trash ;)
     */
    @Override
    protected Result processIDPProblem(final IDPProblem obl,
                          final Abortion abortion) throws AbortionException {
        final IDPToMCSConverter converter = new IDPToMCSConverter();
        final MCSProblem problem = converter.convert(obl, abortion);

        return ResultFactory.proved(problem, YNMImplication.SOUND, new IDPToMCSProof());
    }

    /**
     * A very fine proof.
     *
     * @author cotto (don't blame me), Matthias Hoelzel (don't blame me either ;) )
     */
    public class IDPToMCSProof extends DefaultProof {
        /**
         * Some documentation about the magic we've done.
         */


        /**
         * Create the proof.
         *
         * @param l
         *            Documentation about the magic we've done in the
         *            conversion.
         */
        public IDPToMCSProof() {
            super();
            this.shortName = "IDPToMCSProof";
            this.longName = "IDPToMCSProof";
        }

        /**
         * @param o
         *            export helper
         * @param level
         *            unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "IDPToMCS was executed!";
        }
    }
}
