package aprove.verification.relative.RDTProblem.Processors;

import java.util.HashSet;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.relative.RDTProblem.*;
import immutables.*;

/**
 * Derelatifying Processor as described in Vartanyan's bachelor thesis
 * 
 * @author Grigory Vartanyan
 * @version $Id$
 */
public class RDTDerelatifyingProcessor extends RDTProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isRDTPApplicable(RDTProblem rdpp) {
        return rdpp.isNonRelative();
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processRDTProblem(RDTProblem rdpp, final Abortion aborter) throws AbortionException {

        Set<CoupledPosDepTuple> D = rdpp.getD1();
        Set<Rule> R = rdpp.getQ().getR();  // not too sure this is right

        Set<Rule> depPairs = new HashSet<Rule>();
        for (CoupledPosDepTuple depTuple : D) {  // depTuple is (l#, l) -> (C, r)
            for (Pair<TRSFunctionApplication, Position> pdt : depTuple.getC()) {
                depPairs.add(Rule.create(depTuple.getTupleLeft(), pdt.x));
            }
        }

        QTRSProblem empty_q = QTRSProblem.create(ImmutableCreator.create(R));
        QDPProblem qdpp = QDPProblem.create(ImmutableCreator.create(depPairs), empty_q, false);

        RDTDerelatifyingProof proof = new RDTDerelatifyingProof(rdpp, qdpp);

        final Result result = ResultFactory.proved(qdpp, YNMImplication.EQUIVALENT, proof);
        return result;

    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static class RDTDerelatifyingProof extends RDTProof {

        private final RDTProblem rdpp;
        private final QDPProblem qdpp;

        private RDTDerelatifyingProof(final RDTProblem rdpp, final QDPProblem qdpp) {
            this.rdpp = rdpp;
            this.qdpp = qdpp;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            String res = "";
            res += o.paragraph();
            res += "We use the derelatifying processor " + o.cite(Citation.VARTANYAN_BA) + ".";
            res += o.linebreak();
            res = "There are no relative tuples, so the relative DT problem can be transformed into a non-relative DP problem.";

            res += o.paragraph();
            res += "Resulting in:";
            res += o.linebreak();
            res += qdpp.toString();

            return o.export(res);
        }

    }

    public static class Arguments {

        public boolean beComplete = true;
        public boolean useApplicativeCeRules = true;
    }
}
