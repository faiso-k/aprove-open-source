package aprove.verification.theoremprover.Simplifier;


import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Programs.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Rewriting.Rule;
import aprove.verification.oldframework.Rewriting.Transformers.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TRSProblem.*;
import aprove.verification.theoremprover.TerminationVerifier.*;
import immutables.*;


/**
 * Transformes a SimplifierObligation to TRS
 * @author swiste
 * @version $Id$
 */

@NoParams
public class CurrentMutualRecursiveBlockToTRSProcessor extends Processor.ProcessorSkeleton {

    private Program curprog;
    private Set<DefFunctionSymbol> terminDefs;
    private boolean useKnownTermination;

    public CurrentMutualRecursiveBlockToTRSProcessor() {
        this(false);
    }
    public CurrentMutualRecursiveBlockToTRSProcessor(boolean useKnownTermination) {
        this.useKnownTermination = useKnownTermination;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof SimplifierProblem);
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        SimplifierObligation sObl = ((SimplifierProblem)obl).getSimplifierObligation();
        this.curprog = Program.create(sObl.getCurrentMRBRules(), sObl.program, AbstractProgram.SIMPLIFIED);
        this.curprog.setStrategy(Program.INNERMOST);
        if (this.curprog.isConditional()) {
            this.curprog = this.curprog.transformConditional();
        }

        TRS trs = new TRS(this.curprog, true);


        MRB2DPsProcessor mrb2DPsProc = new MRB2DPsProcessor(sObl.getCurrentMRB(), this.useKnownTermination);
        Result dpsResult = mrb2DPsProc.processProgram(trs, aborter, obl);
        this.terminDefs = mrb2DPsProc.getAlreadyTerminatingDefs();
        return dpsResult;
    }

    public Set<DefFunctionSymbol> getTerminatingDefs() {
        return this.terminDefs;
    }

    private class MRB2DPsProcessor {

        private Set<DefFunctionSymbol> curMRBDefs;


        private Set<DefFunctionSymbol> alreadyTerminatingDefs;
        private boolean useKnownTermination;

        private MRB2DPsProcessor(Set<DefFunctionSymbol> curMRBDefs, boolean useKnownTermination) {
            super();
            this.curMRBDefs = curMRBDefs;
            this.alreadyTerminatingDefs = new HashSet<DefFunctionSymbol>();
            this.useKnownTermination = useKnownTermination;
        }

        /**
         * does almost the same as the original routine, but only looks
         * at the dependency pairs that originated from the current MRB
         */
        public Result processProgram(TRS trs, Abortion aborter, BasicObligation origObl) throws AbortionException {
            Program prog = trs.getProgram();
            boolean innermost = trs.getInnermost();
            prog = prog.transformToReduced();
            Set<Rule> progrules;
            DependencyPairs dps;

            progrules = prog.getRules();
            dps = DependencyPairs.create(progrules, prog.getSignature());

            Iterator<Rule> dp_it = dps.iterator();
            while (dp_it.hasNext()) {
                Rule dp = dp_it.next();
                TupleSymbol tupleSym = (TupleSymbol)dp.getLeft().getSymbol();
                DefFunctionSymbol origDefSym = tupleSym.getOrigin();

                boolean isInCurrentMRB = this.curMRBDefs.contains(origDefSym);

                // it must be the case that the transformation from a conditional to an unconditional TRS
                // presevers If-Symbols. This is the case, since If-Symbols always have rules...
                if ( (!isInCurrentMRB) && (origDefSym instanceof IfSymbol) ) {
                    IfSymbol ifsym = (IfSymbol) origDefSym;
                    String ifsymShortName = ifsym.getShortName();
                    Iterator<DefFunctionSymbol> curMRBDef_it = this.curMRBDefs.iterator();
                    while (!isInCurrentMRB && curMRBDef_it.hasNext()) {
                        isInCurrentMRB |= curMRBDef_it.next().getName().equals(ifsymShortName);
                    }
                }

                if (!isInCurrentMRB) {
                    dp_it.remove();
                }
                else {
                    if (!this.useKnownTermination) {
                        origDefSym.setTermination(false);
                    }
                    if (origDefSym.getTermination()) {
                        this.alreadyTerminatingDefs.add(origDefSym);
                    }
                }
            }

            ImmutableSet<aprove.verification.dpframework.BasicStructures.Rule> R = ImmutableCreator.create(prog.getNewRules());
            Set<TRSFunctionApplication> Q = innermost ? CollectionUtils.getLeftHandSides(R) : new HashSet<TRSFunctionApplication>();
            QTRSProblem qtrs = QTRSProblem.create(R, Q);

            Set<aprove.verification.dpframework.BasicStructures.Rule> P = new HashSet<aprove.verification.dpframework.BasicStructures.Rule>(dps.size());
            for (Rule dp : dps) {
                P.add(dp.toNewRule());
            }

            boolean minimal = true;

            YNMImplication implication = YNMImplication.SOUND;

            QDPProblem qdp = QDPProblem.create(ImmutableCreator.create(P), qtrs, minimal);

            // if one wants this proof for xml-output then one must write a new one,
            // passing null as second argument is only valid when using other proof-outputs!!
            Proof proof = aprove.verification.dpframework.TRSProblem.Processors.DependencyPairsProcessor.createDPProof(qdp, null);


            return ResultFactory.proved(qdp, implication, proof);
        }


        public Set<DefFunctionSymbol> getAlreadyTerminatingDefs() {
            return this.alreadyTerminatingDefs;
        }
    }
}
