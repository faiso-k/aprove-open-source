package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LemmaDatabase.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Implication;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;
@NoParams
public class InverseModusPonensProcessor extends TheoremProverProcessor {

    public InverseModusPonensProcessor() {
        super();
    }

    public InverseModusPonensProcessor(boolean checkLemmaDatabase) {
        super(checkLemmaDatabase);
    }

    @Override
    protected Result process(TheoremProverObligation obligationInput, BasicObligationNode obligationNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {

        InternalProcessor internalProcessor = new InternalProcessor();
        return internalProcessor.process(obligationInput, obligationNode, aborter, rti);

    }

    protected class InternalProcessor {

        protected Set<Implication>     implicationsAlreadyUsed;

        protected Set<Formula>         lemmasAlreadUsed;

        public InternalProcessor() {
            this.lemmasAlreadUsed         = new LinkedHashSet<Formula>();
            this.implicationsAlreadyUsed = new LinkedHashSet<Implication>();
        }

        protected Result process(TheoremProverObligation obligationInput, ObligationNode obligationNode, Abortion aborter, RuntimeInformation rti)throws AbortionException {

            Formula formula = obligationInput.getFormula();

            // calculate implications which are not already used
            Set<Implication> unusedImplications = new LinkedHashSet<Implication>(LemmaDatabaseFactory.
                    getLemmmaDatabase().getAllImplications());
            unusedImplications.removeAll(this.implicationsAlreadyUsed);

            // check if there implications which not used already used
            if(!unusedImplications.isEmpty()) {

                for(Implication implication : unusedImplications) {

                    AlgebraSubstitution substitution = implication.getRight().matches(formula);

                    if( substitution != null) {

                        // add implication to used implications
                        this.implicationsAlreadyUsed.add(implication);

                        // create new obligation
                        Formula newFormula = implication.getLeft().apply(substitution);
                        TheoremProverObligation theoremProverObligation = new TheoremProverObligation(newFormula,obligationInput);

                        return ResultFactory.proved(theoremProverObligation, YNMImplication.SOUND, new InverseModusPonensProof(
                                theoremProverObligation, implication));

                    }

                }

            }

            // calculate formular which are not already used
            Set<Formula> unusedLemmas = new LinkedHashSet<Formula>(LemmaDatabaseFactory.getLemmmaDatabase().retrieveAllFormulas());
            unusedLemmas.removeAll(this.lemmasAlreadUsed);

            // get all subterms of obligation
            Set<AlgebraTerm> subTerms = formula.getAllSubTerms();

            // search for a lemma which shares subterms with the obligation
            for(Formula lemma : unusedLemmas ) {

                Set<AlgebraTerm> lemmaSubterms = lemma.getAllSubTerms();

                for(AlgebraTerm subTerm : subTerms) {

                    if(lemmaSubterms.contains(subTerm)) {

                        // add lemma to used lemmas
                        this.lemmasAlreadUsed.add(lemma);

                        // create new obligation
                        Formula newFormula = Implication.create(lemma.deepcopy(),formula.deepcopy());
                        TheoremProverObligation theoremProverObligation = new TheoremProverObligation(newFormula, obligationInput);

                        return ResultFactory.proved(theoremProverObligation, YNMImplication.SOUND, new InverseModusPonensProof(
                                theoremProverObligation, lemma));

                    }

                }

            }

            return ResultFactory.notApplicable();
        }

    }

}
