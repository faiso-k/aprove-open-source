package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;
import java.util.Map.*;
import java.util.stream.*;

import org.apache.commons.math3.fraction.*;

import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.relative.RelADPProblem.*;
import immutables.*;

/**
 * Upgrades RelTRS Problem to the ADP-based RADPProblem.
 * Theorem: R/B terminating iff RDPP (ADP(R), ADP(B)) terminating
 *
 * @author Grigory Vartanyan
 */
@NoParams
public class RelTRStoRelADPProcessor extends RelTRSProcessor {

    @Override
    public boolean isRelTRSApplicable(RelTRSProblem relTRS) {
        if (Options.certifier.isCeta()) {
            return false;
        }
        
        return !relTRS.isSDuplicating();
    }
    
    @Override
    protected Result processRelTRS(
        final RelTRSProblem relTRS,
        final Abortion aborter,
        final RuntimeInformation rti
    ) throws AbortionException {

        
        if (relTRS.isSDuplicating()) {
            return ResultFactory.notApplicable();
        }
        
        var ADPData = relTRS.getRelativeADPs();
        var ADPPair = ADPData.x;
        var annotator = ADPData.y;

        Set<Rule> R = new HashSet<>();
        R.addAll(relTRS.getR());
        R.addAll(relTRS.getS());
        var Q = QTRSProblem.create(ImmutableCreator.create(R));
        
        BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap = BidirectionalMap.create(annotator);
        
        final RelADPProblem relADP = RelADPProblem.create(ADPPair.x, ADPPair.y, Q, annoMap);
        return ResultFactory.proved(relADP, YNMImplication.EQUIVALENT, new RelTRStoRelADPProof());
    }

    public static class RelTRStoRelADPProof extends RelTRSProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            String res = "";
            res += o.paragraph();
            res += "We upgrade the RelTRS problem to an equivalent Relative ADP Problem ";
            res += o.cite(Citation.IJCAR24) + ".";
            res += o.cond_linebreak();

            return o.export(res);
        }

    }
}
