package aprove.verification.dpframework.PiDPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.PiDPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

@NoParams
public class PiDPToQDPProcessor extends PiDPProblemProcessor {

    @Override
    public boolean isPiDPApplicable(AbstractPiDPProblem apidp) {
        return apidp instanceof PiDPProblem;
    }

    @Override
    protected Result processPiDPProblem(AbstractPiDPProblem apidp,
        Abortion aborter) throws AbortionException {
        if (Globals.useAssertions) {
            assert (this.isApplicable(apidp));
        }
        PiDPProblem pidp = (PiDPProblem) apidp;
        Afs Pi = pidp.getPi();
        Set<GeneralizedRule> P = Pi.filterGeneralizedRules(pidp.getP());
        Set<GeneralizedRule> R = Pi.filterGeneralizedRules(pidp.getR());
        Set<TRSFunctionApplication> Q = PiDPToQDPProcessor.symbolToApplication(CollectionUtils.getRootSymbols(R));
        QTRSProblem qtrs = QTRSProblem.create(ImmutableCreator.create(Rule.fromGeneralizedRules(R)), Q);
        QDPProblem qdp = QDPProblem.create(ImmutableCreator.create(Rule.fromGeneralizedRules(P)),qtrs,false);
        Implication implication = Pi.isEmpty() ? YNMImplication.EQUIVALENT : YNMImplication.SOUND;
        Proof proof = new PiDPToQDPProof();
        return ResultFactory.proved(qdp, implication, proof);

    }

    private static Set<TRSFunctionApplication> symbolToApplication(Set<FunctionSymbol> rootSymbols) {
        Set<TRSFunctionApplication> fapps = new LinkedHashSet<TRSFunctionApplication>();
        for (FunctionSymbol f : rootSymbols) {
            ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
            for (int i = 1; i <= f.getArity(); i++) {
                args.add(TRSTerm.createVariable("x"+i));
            }
            fapps.add(TRSTerm.createFunctionApplication(f, ImmutableCreator.create(args)));
        }
        return fapps;
    }

    private static class PiDPToQDPProof extends Proof.DefaultProof {

        private PiDPToQDPProof() {
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Transforming (infinitary) constructor rewriting Pi-DP problem "+o.cite(Citation.LOPSTR)+" into ordinary QDP problem "+o.cite(Citation.LPAR04)+" by application of Pi.";
        }

    }

}
