package aprove.verification.theoremprover.TheoremProverProcedures;

/**
 * This visitor is the LemmaApplicationVisitor which was an inner class of
 * the LemmaApplicationProcessor in Revision 1.17 by rabe.
 *
 * This visitor works well for the examples of the Boyer-Moore corpus.
 *
 * However:
 * The variables of the lemma or not replaced by fresh new variables.
 * Implications (& equivalences) are not applied.
 * Equations are only applied from left to right.
 * Equations are not applied on equations.
 *  (This is not a real restriction since after applying them from left to right
 *   a symbolic evaluation is performed which will lead to that result.)
 * Equations are not applied on variables.
 * A lemma is maximally applied once.
 *
 * (Read the processor help for more information.)
 *
 * @author dickmeis
 * @version $Id$
 */

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


class LemmaApplicationVisitorOld implements FineFormulaVisitor<Formula>, CoarseGrainedTermVisitor<AlgebraTerm> {

    protected Set<Formula> lemmas;
    protected Set<Formula> usedLemmas;

    public static Pair<Formula,Set<Formula>> apply(Formula formula, Set<Formula> lemmas) {
        LemmaApplicationVisitorOld lemmaApplicationVisitor = new LemmaApplicationVisitorOld(lemmas);
        return new Pair<Formula,Set<Formula>>(formula.apply(lemmaApplicationVisitor),lemmaApplicationVisitor.usedLemmas);
    }

    protected LemmaApplicationVisitorOld(Set<Formula> lemmas) {
        this.lemmas = lemmas;
        this.usedLemmas = new LinkedHashSet<Formula>();
    }

    @Override
    public Formula caseEquation(Equation eqFormula) {
        return Equation.create(eqFormula.getLeft().apply(this),eqFormula.getRight().apply(this));
    }

    @Override
    public Formula caseAnd(And andFormula) {
        return And.create(andFormula.getLeft().apply(this),andFormula.getRight().apply(this));
    }

    @Override
    public Formula caseEquivalence(Equivalence equivFormula) {
        return Equivalence.create(equivFormula.getLeft().apply(this),equivFormula.getRight().apply(this));
    }

    @Override
    public Formula caseImplication(Implication implFormula) {
        return Implication.create(implFormula.getLeft().apply(this),implFormula.getRight().apply(this));
    }

    @Override
    public Formula caseNot(Not notFormula) {
        return Not.create(notFormula.getLeft().apply(this));
    }

    @Override
    public Formula caseOr(Or orFormula) {
        return Or.create(orFormula.getLeft().apply(this),orFormula.getRight().apply(this));
    }

    @Override
    public Formula caseTruthValue(FormulaTruthValue truthvalFormula) {
        return truthvalFormula.deepcopy();
    }

    @Override
    public AlgebraTerm caseFunctionApp(AlgebraFunctionApplication f) {

        Iterator<Formula> iterator = this.lemmas.iterator();
        while(iterator.hasNext()) {
            Formula lemma = iterator.next();
            if(lemma instanceof Equation) {
                Equation equation = (Equation)lemma;
                try {
                    AlgebraSubstitution substitution = equation.getLeft().matches(f);
                    this.usedLemmas.add(lemma);
                    iterator.remove();
                    return equation.getRight().apply(substitution);
                }catch(UnificationException e) {}
            }
        }

        List<AlgebraTerm> arguments = new ArrayList<AlgebraTerm>();
        for(AlgebraTerm argument : f.getArguments()) {
            arguments.add(argument.apply(this));
        }

        return AlgebraFunctionApplication.create(f.getFunctionSymbol(), arguments);
    }

    @Override
    public AlgebraTerm caseVariable(AlgebraVariable v) {
        return v.deepcopy();
    }

}