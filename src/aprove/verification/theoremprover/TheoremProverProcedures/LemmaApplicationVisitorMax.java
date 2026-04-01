package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TheoremProverProcedures.LemmaDirectors.*;

/**
 * Compared to LemmaApplicationVisitorOld:
 * - Lemma application (of equations) is done in caseFunctionApp form right to left, too.
 * - The amount of lemma applications is counted and
 *   further application is canceled if a limit (sequenceLength) is reached.
 *   (If sequenceLength is set to 0, applications are done as long as possible.
 * - There is the optinal heuristic of applying equations only in the direction (from side 1 to side 2)
 *   for which side 1 is greater than side 2 regarding a globally given order.
 *   If this heuristic is used it will also be tried to apply program rules
 *   for which the left side is greater than the right side regarding a globally given order.
 *
 * Implications (& equivalences) are not applied.
 * Equations are not applied on equations.
 *  (This is not a real restriction since after applying them in a direction
 *   symbolic evaluation is performed which will lead to that result.)
 * A lemma is maximally applied once if not using the heuristic of applying lemmas only in one direction.
 * The variables of the lemma or not replaced by fresh new variables.
 *
 * (Read the processor help for more information.)
 *
 * @author dickmeis
 * @version $Id$
 */

class LemmaApplicationVisitorMax implements FineFormulaVisitor<Formula>, CoarseGrainedTermVisitor<AlgebraTerm> {

    protected Set<Formula> lemmas;
    protected Set<Formula> usedLemmas;
    protected LemmaDirector lemmaDirector;
    protected ArrayList<Rule> programRules;
    protected int sequenceLength;
    protected int actualSequenceLength;

    public static Pair<Formula,Set<Formula>> apply(Formula formula, Set<Formula> lemmas, LemmaDirector lemmaDirector, Set<Rule> rules, int length) {
        LemmaApplicationVisitorMax lemmaApplicationVisitor = new LemmaApplicationVisitorMax(lemmas, lemmaDirector, rules, length);
        return new Pair<Formula,Set<Formula>>(formula.apply(lemmaApplicationVisitor),lemmaApplicationVisitor.usedLemmas);
    }

    protected LemmaApplicationVisitorMax(Set<Formula> lemmas, LemmaDirector lemmaDirector, Set<Rule> rules, int length) {
        this.lemmas = lemmas;
        this.usedLemmas = new LinkedHashSet<Formula>();
        this.lemmaDirector = lemmaDirector;
        this.sequenceLength = length;
        this.actualSequenceLength = 0;

        for (Rule rule : rules) {
            this.programRules = new ArrayList<Rule>();
            // take only unconditional rules
            if (rule.getConds().isEmpty()){
                this.programRules.add(rule);
            }
        }
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
    public Formula caseEquation(Equation eqFormula) {
        AlgebraTerm left = eqFormula.getLeft();
        if (this.sequenceLength == 0 || this.actualSequenceLength < this.sequenceLength){
            left = left.apply(this);
        }
        AlgebraTerm right = eqFormula.getRight();
        if (this.sequenceLength == 0 || this.actualSequenceLength < this.sequenceLength){
            right = right.apply(this);
        }
        Equation eq = Equation.create(left,right);
        if (!eq.equals(eqFormula)){
            return this.caseEquation(eq);
        }
        return eq;
    }

    @Override
    public Formula caseTruthValue(FormulaTruthValue truthvalFormula) {
        return truthvalFormula.deepcopy();
    }

    @Override
    public AlgebraTerm caseFunctionApp(AlgebraFunctionApplication f) {

        boolean applicated = false;
        AlgebraTerm newF=f;

        if (this.sequenceLength == 0 || this.actualSequenceLength < this.sequenceLength){

            Iterator<Formula> iterator = this.lemmas.iterator();

            while(iterator.hasNext() && !applicated ) {
                Formula lemma = iterator.next();
                if(lemma instanceof Equation) {
                    Equation equation = (Equation)lemma;

                    AlgebraSubstitution substitution=null;
                    boolean matchFound=false;
                    boolean applicable=false;

                    // first try to apply the lemma left to right
                    try {
                        substitution = equation.getLeft().matches(f);
                        matchFound=true;
                        }
                    catch(UnificationException e) {
                        matchFound=false;
                    }

                    if (matchFound){
                        if(this.lemmaDirector!=null){
                            // check if it can be orientated
                            Rule rule;
                            AlgebraTerm l = equation.getLeft();
                            AlgebraTerm r = equation.getRight();

                            // first try l > r
                            rule = Rule.create(l, r);
                            applicable = this.lemmaDirector.extendByRule(rule);
                        }
                        else{
                            // otherwise it is appliable by default
                            applicable = true;
                        }

                        if(applicable){
                            this.usedLemmas.add(lemma);
                            if(this.lemmaDirector==null){
                                // if we use the heuristic of applying only orientable lemmas
                                // we do not use the heuristic of applying leammas only once
                                iterator.remove();
                            }
                            this.actualSequenceLength++;
                            applicated = true;
                            newF = equation.getRight().apply(substitution);
                        }
                    }

                    if(!applicated){
                        matchFound=false;
                        // otherwise try to apply the lemma right to left
                        try {
                            substitution = equation.getRight().matches(f);
                            matchFound=true;
                            }catch(UnificationException e) {
                            matchFound=false;
                        }

                        if (matchFound){
                            if(this.lemmaDirector!=null){
                                // check if it can be orientated
                                Rule rule;
                                AlgebraTerm l = equation.getLeft();
                                AlgebraTerm r = equation.getRight();

                                // first try r > l
                                rule = Rule.create(r, l);
                                applicable = this.lemmaDirector.extendByRule(rule);
                            }
                            else{
                                // otherwise it is appliable by default
                                applicable = true;
                            }

                            if(applicable){
                                if(this.lemmaDirector==null){
                                    // if we use the heuristic of applying only orientable lemmas
                                    // we do not use the heuristic of applying leammas only once
                                    this.usedLemmas.add(lemma);
                                    iterator.remove();
                                }
                                this.actualSequenceLength++;
                                applicated = true;
                                newF = equation.getLeft().apply(substitution);
                            }
                        }
                    }
                }
            }
        }

        if (!applicated){
            if(this.lemmaDirector!=null){
                // try to apply program rules
                for (Rule rule : this.programRules) {

                    AlgebraSubstitution substitution=null;
                    boolean matchFound=false;
                    boolean applicable=false;

                    try {
                        substitution = rule.getLeft().matches(f);
                        matchFound=true;
                        }catch(UnificationException e) {
                        matchFound=false;
                    }

                    if (matchFound){
                        if(this.lemmaDirector!=null){
                            // check if it can be orientated (l > r)
                            applicable = this.lemmaDirector.extendByRule(rule);
                        }
                        else{
                            // otherwise it is appliable by default
                            applicable = true;
                        }

                        if(applicable){
                            this.actualSequenceLength++;
                            applicated = true;
                            newF = rule.getRight().apply(substitution);
                        }
                    }
                }
            }
        }

        if(!applicated){
            List<AlgebraTerm> arguments = new ArrayList<AlgebraTerm>();
            for(AlgebraTerm argument : f.getArguments()) {
                arguments.add(argument.apply(this));
            }
            newF = AlgebraFunctionApplication.create(f.getFunctionSymbol(), arguments);
        }

        if (!newF.equals(f) && newF instanceof AlgebraFunctionApplication){
            // something has changed, so go over it again
            // newF can be a variable, too
            return this.caseFunctionApp((AlgebraFunctionApplication) newF);
        }
        return newF;
    }

    @Override
    public AlgebraTerm caseVariable(AlgebraVariable v) {
        return v.deepcopy();
    }

}