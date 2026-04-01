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
public class PiDependencyPairsProcessor extends PiTRSProcessor {

    @Override
    protected Result processPiTRS(AbstractPiTRSProblem apitrs, Abortion aborter)
            throws AbortionException {
        PiTRSProblem pitrs = (PiTRSProblem) apitrs;
        Pair<ImmutableSet<GeneralizedRule>,Map<FunctionSymbol, FunctionSymbol>> pair = pitrs.getDPs();
        ImmutableSet<GeneralizedRule> P = pair.x;
        ImmutableSet<GeneralizedRule> R = pitrs.getR();
        Afs newPi = pitrs.getPi().addTuples(pair.y);
        Set<GeneralizedRule> PcupR = new LinkedHashSet<GeneralizedRule>(P);
        PcupR.addAll(R);
        PiDependencyPairsProcessor.extendPi(newPi, PcupR);
        PiTRSProblem newPitrs = PiTRSProblem.create(R, new ImmutableAfs(newPi));
        PiDPProblem pidpProblem = PiDPProblem.create(P, newPitrs);
        return ResultFactory.proved(pidpProblem, YNMImplication.EQUIVALENT, new DependencyPairsProof(pidpProblem));
    }

    @Override
    public boolean isPiTRSApplicable(AbstractPiTRSProblem apitrs) {
        return apitrs instanceof PiTRSProblem;
    }

    public static void extendPi(Afs Pi, Set<GeneralizedRule> R) {
        boolean tryToExtend = true;
        while (tryToExtend) {
            tryToExtend = false;
            for (GeneralizedRule rule : R) {
                tryToExtend = PiDependencyPairsProcessor.extendPi(Pi, rule) || tryToExtend;
            }
        }
    }
    private static boolean extendPi(Afs Pi, GeneralizedRule rule) {
        Set<TRSVariable> lvars = Pi.filterTerm(rule.getLeft()).getVariables();
        Set<TRSVariable> rvars = Pi.filterTerm(rule.getRight()).getVariables();
        Set<TRSVariable> evilVars = new LinkedHashSet<TRSVariable>(rvars);
        evilVars.removeAll(lvars);
        if (!evilVars.isEmpty()) {
            //System.err.println("Evil vars ins "+rule+": "+evilVars);
            return PiDependencyPairsProcessor.extendPi(Pi, (TRSFunctionApplication)rule.getRight(), evilVars);
        }
        return false;
    }

    private static boolean extendPi(Afs Pi, TRSFunctionApplication fapp, Set<TRSVariable> evilVars) {
        FunctionSymbol f = fapp.getRootSymbol();
        ImmutableList<? extends TRSTerm> args = fapp.getArguments();
        boolean[] regarded = Pi.getRegardedArgs(f);
        YNM[] newArgs = new YNM[regarded.length];
        boolean changed = false;
        for (int i = 0; i < regarded.length; i++) {
            if (regarded[i]) {
                TRSTerm argi = args.get(i);
                if (argi.isVariable()) {
                    if (evilVars.contains(argi)) {
                        newArgs[i] = YNM.NO;
                        changed = true;
                    } else {
                        newArgs[i] = YNM.YES;
                    }
                } else {
                    changed = PiDependencyPairsProcessor.extendPi(Pi, (TRSFunctionApplication)argi, evilVars) || changed;
                    newArgs[i] = YNM.YES;
                }
            } else {
                newArgs[i] = YNM.NO;
            }
        }
        if (changed) {
            Pi.setFiltering(f, newArgs);
        }
        return changed;
    }


    /**
     * Proof which prints out the resulting QDPProblem
     *
     * @author Matthias Sondermann
     * @version $Id$
     */
    private class DependencyPairsProof extends Proof.DefaultProof{

        PiDPProblem pidpProblem;

        private DependencyPairsProof(PiDPProblem pidpProblem) {
            this.pidpProblem = pidpProblem;
        }
        @Override
        public String export(Export_Util eu, VerbosityLevel level){
            return "Using Dependency Pairs "+eu.cite(new Citation[]{Citation.AG00, Citation.LOPSTR})+" we result in the following initial DP problem:"+eu.linebreak()+this.pidpProblem.export(eu);
        }
    }
}
