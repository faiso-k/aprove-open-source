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

/**
 *
 * @author dickmeis
 * @version $Id: ConditionalRewritingProcessor.java,v 1.3 2006/10/19 11:42:37
 *          dickmeis Exp $
 */
@NoParams
public class ReverseImplicationApplicationProcessor extends TheoremProverProcessor {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof TheoremProverObligation) {
            // only for indirect proofs
            TheoremProverObligation theorem_obl = (TheoremProverObligation) obl;
            return theorem_obl.isIndirectProof();
        }
        return false;
    }

    @Override
    protected Result process(TheoremProverObligation obligationInput,
            BasicObligationNode obligationNode, Abortion aborter,
            RuntimeInformation rti) throws AbortionException {

        Formula formula = obligationInput.getFormula();

        LemmaDatabase ldb = LemmaDatabaseFactory.getLemmmaDatabase();

        Set<Implication> implications = ldb.getAllImplications();

        Formula newFormula = null;

        for (Implication implication : implications) {
            ImplicationApplicationVisitor implicationApplicationVisitor =
                new ImplicationApplicationVisitor(implication);

            newFormula = formula.apply(implicationApplicationVisitor);

            if (implicationApplicationVisitor.done){

                TheoremProverObligation newObligation = new TheoremProverObligation(
                                                                newFormula,
                                                                obligationInput);

                ReverseImplicationApplicationProof proof = new ReverseImplicationApplicationProof(
                                                                    implication, newObligation);

                return ResultFactory.proved(newObligation,
                                            YNMImplication.COMPLETE,
                                            proof);
            }
        }

        return ResultFactory.notApplicable();
    }

}

class ImplicationApplicationVisitor implements FineFormulaVisitor<Formula> {

    Formula implLeft;
    Formula implRight;
    boolean done;

    public ImplicationApplicationVisitor(Implication implication) {
        this.implLeft = implication.getLeft();
        this.implRight = implication.getRight();
        this.done = false;
    }

    private Formula try2apply(Formula formula){
        AlgebraSubstitution substitution = this.implLeft.matches(formula);

        if (substitution == null){
            return formula;
        }
        else {
            Formula newFormula = this.implRight.apply(substitution);
            this.done = true;
            return newFormula;
        }
    }

    @Override
    public Formula caseAnd(And andFormula) {
        Formula newFormula;

        newFormula = this.try2apply(andFormula);
        if(this.done){
            return newFormula;
        }

        Formula left = andFormula.getLeft();
        Formula right = andFormula.getRight();

        newFormula = left.apply(this);
        if(this.done){
            And newAnd = And.create(newFormula, right);
            return newAnd;
        }

        newFormula = right.apply(this);

        And newAnd = And.create(left, newFormula);

        return newAnd;
    }

    @Override
    public Formula caseEquation(Equation phi) {
        return this.try2apply(phi);
    }

    @Override
    public Formula caseEquivalence(Equivalence equivFormula) {
        Formula newFormula = this.try2apply(equivFormula);
        if(this.done){
            return newFormula;
        }

        // do not descend side because of the implicit negation
        //TODO idea: transform to implications and apply then

        return equivFormula;
    }

    @Override
    public Formula caseImplication(Implication implFormula) {
        Formula newFormula;

        newFormula = this.try2apply(implFormula);
        if(this.done){
            return newFormula;
        }

        Formula left = implFormula.getLeft();
        Formula right = implFormula.getRight();

        // do not descend on the left side because of the implicit negation
        //TODO idea: transform to or and apply then

        newFormula = right.apply(this);

        Implication newOr = Implication.create(left, newFormula);

        return newOr;
    }

    @Override
    public Formula caseNot(Not notFormula) {
        Formula newFormula = this.try2apply(notFormula);
        if(this.done){
            return newFormula;
        }

        // do not descend because of the negation
        //TODO Idea: Count the negations

        return notFormula;
    }

    @Override
    public Formula caseOr(Or orFormula) {
        Formula newFormula;

        newFormula = this.try2apply(orFormula);
        if(this.done){
            return newFormula;
        }

        Formula left = orFormula.getLeft();
        Formula right = orFormula.getRight();

        newFormula = left.apply(this);
        if(this.done){
            Or newOr = Or.create(newFormula, right);
            return newOr;
        }

        newFormula = right.apply(this);

        Or newOr = Or.create(left, newFormula);

        return newOr;
    }

    /**
     * Nothing to do
     */
    @Override
    public Formula caseTruthValue(FormulaTruthValue truthvalFormula) {
        return truthvalFormula;
    }

}