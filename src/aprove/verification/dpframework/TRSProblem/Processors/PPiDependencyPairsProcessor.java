package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.PiDPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Processor which creates out of a given QTRS a new QDPProblem where P contains all dependency pairs of R.
 *
 * @author Matthias Sondermann
 * @version $Id$
 */

@NoParams
public class PPiDependencyPairsProcessor extends PiTRSProcessor {

    @Override
    protected Result processPiTRS(AbstractPiTRSProblem apitrs, Abortion aborter)
            throws AbortionException {
        PPiTRSProblem pitrs = (PPiTRSProblem) apitrs;
        Pair<ImmutableSet<GeneralizedRule>,Map<FunctionSymbol, FunctionSymbol>> pair = pitrs.getDPs();
        ImmutableSet<GeneralizedRule> P = pair.x;
        ImmutableSet<GeneralizedRule> R = pitrs.getR();

        ImmutableSet<FunctionSymbol> symbols_in_pi =
            pitrs.getPi().getFunctionSymbols();
        Map<FunctionSymbol, FunctionSymbol> tuple_symbols_in_pi = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();
        for(FunctionSymbol f : symbols_in_pi) {
            if( pair.y.containsKey(f)) {
            tuple_symbols_in_pi.put(f, pair.y.get(f));
            }
        }
        Afs newPi = pitrs.getPi().addTuples(tuple_symbols_in_pi);

        PPiTRSProblem newPitrs = PPiTRSProblem.create(R, new ImmutableAfs(newPi), pitrs.getStartSymbol());
        PPiDPProblem pidpProblem = PPiDPProblem.create(P, newPitrs);

        return ResultFactory.proved(pidpProblem, YNMImplication.EQUIVALENT, new DependencyPairsProof(pidpProblem));
    }

    @Override
    public boolean isPiTRSApplicable(AbstractPiTRSProblem apitrs) {
        return apitrs instanceof PPiTRSProblem;
    }


    /**
     * Proof which prints out the resulting QDPProblem
     *
     * @author Matthias Sondermann
     * @version $Id$
     */
    private class DependencyPairsProof extends Proof.DefaultProof{

        PPiDPProblem ppidpProblem;

        private DependencyPairsProof(PPiDPProblem ppidpProblem) {
            this.ppidpProblem = ppidpProblem;
        }
        @Override
        public String export(Export_Util eu, VerbosityLevel level){
            return "Using Dependency Pairs "
                + eu.cite(new Citation[] { Citation.AG00, Citation.LOPSTR })
                + " we result in the following initial partial DP problem:"
                + eu.linebreak() + this.ppidpProblem.export(eu);
        }
    }
}
