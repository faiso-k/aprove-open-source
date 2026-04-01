package aprove.verification.relative.RelADPProblem.Processors;

import java.util.HashSet;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.relative.RelADPProblem.*;
import immutables.*;

/**
 * Derelatifying Processor as described in [IJCAR24]
 * 
 * @author Grigory Vartanyan, Jan-Christoph Kassing
 * @version $Id$
 */
public class RelADPDerelatifyToDPsProcessor extends RelADPProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isRelADPPApplicable(RelADPProblem reladpp) {
        return reladpp.isNonRelative();
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processRelADPProblem(RelADPProblem origreladpp, final Abortion aborter) throws AbortionException {
        Set<Rule> depPairs = new HashSet<Rule>();

        for (Rule adp: origreladpp.getPAbs()) {
            // For absolute ADPs, annotate root positions of left and right
            // and deannotate everything else

            // lhs is has no annotations, annotate root only
            TRSFunctionApplication lhs = adp.getLeft();
            lhs = lhs.renameAtMap(Position.EPSILON, origreladpp.getAnnotator());

            // use each sub dependency term of rhs
            for (TRSFunctionApplication subterm: adp.getRight().subAnnoTerms(origreladpp.getDeannotator())) {
                depPairs.add(Rule.create(lhs, subterm));
            }
        }

        QDPProblem qdpp = QDPProblem.create(ImmutableCreator.create(depPairs), origreladpp.getQ(), false);

        RelADPDerelatifyingProof proof = new RelADPDerelatifyingProof(origreladpp, qdpp);

        final Result result = ResultFactory.proved(qdpp, YNMImplication.EQUIVALENT, proof);
        return result;
    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static class RelADPDerelatifyingProof extends RelADPProof {

        private final RelADPProblem reladpp;
        private final QDPProblem newqdpp;

        private RelADPDerelatifyingProof(final RelADPProblem reladpp, final QDPProblem newqdpp) {
            this.reladpp = reladpp;
            this.newqdpp = newqdpp;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            String res = "";
            res += o.paragraph();
            res += "We use the first derelatifying processor " + o.cite(Citation.IJCAR24) + ".";
            res += o.linebreak();
            res += "There are no annotations in relative ADPs, so the relative ADP problem can be transformed into a non-relative DP problem.";

            return o.export(res);
        }

    }
}
