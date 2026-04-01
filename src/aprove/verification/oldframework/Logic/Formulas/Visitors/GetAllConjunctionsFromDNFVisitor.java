package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Logic.Formulas.*;

/**
 * Given a DNF of the form \Bigvee_{0 < i < n} \psi_i
 * it constructs the set with all conjunctions, equations and Truthvalues { \psi_i | 0 < i < n }
 *
 * @author dickmeis
 * @version $Id$
 *
 */

public class GetAllConjunctionsFromDNFVisitor implements FineFormulaVisitor<Formula>{

    public static List<Formula> apply(Formula formula) {

        GetAllConjunctionsFromDNFVisitor getAllConjunctionsVisitor = new GetAllConjunctionsFromDNFVisitor();

        formula.apply(getAllConjunctionsVisitor);

        List<Formula> allConjunctions = getAllConjunctionsVisitor.getAllConjunctions();

        return allConjunctions;
    }

    private List<Formula> getAllConjunctions() {
        return this.allConjunctions;
    }

    private List<Formula> allConjunctions;

    private GetAllConjunctionsFromDNFVisitor(){
        this.allConjunctions = new ArrayList<Formula>();
    }

    /**
     * Evaluates a subformula of the form "leftFormula /\ rightFormula"
     *
     * Collect this whole formula
     */
    @Override
    public Formula caseAnd(And andFormula) {

        this.allConjunctions.add(andFormula);

        return null;
    }

    /**
     * Evaluates an equation
     *
     * Collect this equation
     */
    @Override
    public Formula caseEquation(Equation phi) {

        this.allConjunctions.add(phi);

        return null;
    }

    /**
     * Evaluates a subformula of the form "leftFormula <--> rightFormula"
     *
     * ERROR
     */
    @Override
    public Formula caseEquivalence(Equivalence equivFormula) {

        throw new RuntimeException("There is an equivalence in a DNF");
    }

    /**
     * Evaluates a subformula of the form "leftFormula --> rightFormula"
     *
     * ERROR
     */
    @Override
    public Formula caseImplication(Implication implFormula) {

        throw new RuntimeException("There is an implication in a DNF");
    }

    /**
     * Evaluates a subformula of the form "~ formula"
     *
     * Collect this whole formula as we handle only DNFs
     */
    @Override
    public Formula caseNot(Not notFormula) {

        this.allConjunctions.add(notFormula);

        return null;
    }

    /**
     * Evaluates a subformula of the form "leftFormula \/ rightFormula"
     *
     * Descend
     */
    @Override
    public Formula caseOr(Or orFormula) {
        Formula left = orFormula.getLeft();
        Formula right = orFormula.getRight();

        left.apply(this);
        right.apply(this);

        return null;
    }

    /**
     * Evaluates a truthvalue.
     *
     * This is unlikely to happen, normally it gets handeled by symbolic evaluation already before.
     *
     * Collect this truthvalue
     */
    @Override
    public Formula caseTruthValue(FormulaTruthValue truthvalFormula) {

        this.allConjunctions.add(truthvalFormula);

        return null;
    }
}