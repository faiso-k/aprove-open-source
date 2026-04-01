package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.oldframework.Algebra.Orders.Solvers.*;
import aprove.verification.oldframework.LemmaApplication.*;
import aprove.verification.oldframework.LemmaDatabase.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TheoremProverProcedures.LemmaDirectors.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

/**
 * In mode OLD a lemma is maximally applied once.
 * In mode MAX without a lemmaDirector a lemma is maximally applied once.
 */
public class LemmaApplicationProcessor extends TheoremProverProcessor {

    // The parameter "order" is configured via the solverFactory.
    // Normally, the solverFactory creates a solver for the desired order.
    // Later it will create a lemmaDirector for the desired order.
    private final SolverFactory solverFactory;
    private final int minimalHeuristic;

    private final int sequenceLength;

    private final LemmaApplicationVisitors mode;

    /**
     * constructor used by param manager via reflection
     */
    @ParamsViaArgumentObject
    public LemmaApplicationProcessor(Arguments arguments) {
        super(false);
        this.minimalHeuristic = arguments.minimalHeuristic;
        this.solverFactory = arguments.order;
        this.sequenceLength = arguments.sequenceLength;
        this.mode = arguments.mode;
    }

    @Override
    protected Result process(TheoremProverObligation obligationInput, BasicObligationNode obligationNode, Abortion aborter,
                RuntimeInformation rti) throws AbortionException {

        // get lemmaDirectorConfiguration
        HashSet lemmaDirectorConfiguration = obligationInput.getLemmaDirectorConfiguration();
        LemmaDirector lemmaDirector = null;

        if (this.mode == LemmaApplicationVisitors.MAX){
            if(this.solverFactory != null){
                Collection<Constraint<TRSTerm>> cons = new HashSet<Constraint<TRSTerm>>();
                AbortableConstraintSolver<TRSTerm> solver = this.solverFactory.getSolver(cons);
                if (solver instanceof LemmaDirectorFactory) {
                    Program p = obligationInput.getProgram();
                    LemmaDirectorFactory lof = (LemmaDirectorFactory) solver;
                    lemmaDirector = lof.getLemmaDirector(p, this.minimalHeuristic);
                    if (lemmaDirectorConfiguration != null){
                        lemmaDirector.setSolverConfiguration(lemmaDirectorConfiguration);
                    }
                }
                else{
                    return ResultFactory.error("This type of order is not implemented for lemma orientation!");
                }
            }
        }

        // get formula
        Formula formula = obligationInput.getFormula();

        Set<Formula> lemmas;

        // get lemmas
        lemmas = LemmaDatabaseFactory.getLemmmaDatabase().retrieveAllFormulas();

        if (this.mode == LemmaApplicationVisitors.MAX || this.mode == LemmaApplicationVisitors.OLD){

            // if we use the heuristic of applying only orientable lemmas
            // we do not use the heuristic of applying leammas only once
            if (this.solverFactory == null){
                lemmas.removeAll(obligationInput.getLemmasUsedSoFar());
            }

            Pair<Formula,Set<Formula>> result = new Pair<Formula,Set<Formula>>(null, null);

            if (this.mode == LemmaApplicationVisitors.MAX){
                result = LemmaApplicationVisitorMax.apply(formula, lemmas, lemmaDirector, obligationInput.getProgram().getRules(),this.sequenceLength);
            }
            else{
                result = LemmaApplicationVisitorOld.apply(formula, lemmas);
            }

            if(formula.equals(result.x)) {
                return ResultFactory.notApplicable();
            }

            TheoremProverObligation newObligation = new TheoremProverObligation(result.x,obligationInput);
            newObligation.addUsedLemmas(result.y);
            if (lemmaDirector != null){
                newObligation.setLemmaDirectorConfiguration(lemmaDirector.getSolverConfiguration());
            }

            LemmaApplicationProofOld lap = new LemmaApplicationProofOld(newObligation,result.y);

            if (this.mode == LemmaApplicationVisitors.OLD){
                return ResultFactory.proved(newObligation,YNMImplication.EQUIVALENT, lap);
            }
            else {
                // possible use of implications
                return ResultFactory.proved(newObligation,YNMImplication.SOUND, lap);
            }
        }
        else{
            // this.mode == LemmaApplicationVisitors.ALL

            // because we avoid circularities by checking
            // if our actual formula to prove had already to be proved before
            // (contained in ancestorFormulas)
            // we allow that all lemmas can be applied

            ArrayList<LemmaApplicationResult> results = LemmaApplicationVisitorAll.apply(formula, lemmas);

            if(results.isEmpty()) {
                return ResultFactory.notApplicable();
            }

            results.iterator();

            for (int i = 0; i < results.size(); i++) {
                LemmaApplicationResult r1 = results.get(i);
                for (int j = i; j < results.size(); j++) {
                    LemmaApplicationResult r2 = results.get(j);
                    if (!r1.equals(r2) &&
                            r1.getResult().equals(r2.getResult()) &&
                            r1.getLemma().equals(r2.getLemma()))
                        // the same result is generated by using the same lemma
                        // (but at different positions)
                        // so we can ignore one
                        {
                        r2.setUnusful();
                        // do the deletion afterwards to not endanger the array bounds
                    }
                }
            }

            Set<Formula> ancestorFormulas = obligationInput.getAncestorFormulas();

            for (Iterator iter = results.iterator(); iter.hasNext();) {
                LemmaApplicationResult r = (LemmaApplicationResult) iter.next();

                // do the deltion from before
                if (r.getUtilityEstimation() == LemmaApplicationResult.UnusefulValue){
                    iter.remove();
                    continue;
                }

                if (ancestorFormulas.contains(r.getResult())){
                    r.setUnusful();
                    iter.remove();
                }
            }

            Collections.sort(results);
            Collections.reverse(results);

            ArrayList<TheoremProverObligation> newObligations = new ArrayList<TheoremProverObligation>();

            for (LemmaApplicationResult r : results) {
                TheoremProverObligation newObligation = new TheoremProverObligation(r.getResult(),obligationInput);

                ArrayList<Formula> usedLemmas = new ArrayList<Formula>();
                usedLemmas.add(r.getLemma());
                newObligation.addUsedLemmas(usedLemmas);

                newObligations.add(newObligation);
            }

            LemmaApplicationProof lap = new LemmaApplicationProof(results);

            // possible use of implications
            return ResultFactory.provedOr(newObligations,YNMImplication.SOUND, lap);
        }
    }

    public static class Arguments {
        public int minimalHeuristic = 1;
        /* the mode which has to be used */
        public LemmaApplicationVisitors mode = LemmaApplicationVisitors.OLD;
        /* indicates which LemmaDirector to use */
        public SolverFactory order = null;
        public int sequenceLength = 0;
    }

}