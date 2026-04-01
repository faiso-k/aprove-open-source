package aprove.verification.theoremprover.TheoremProverProcedures;

/**
 * By this all possible lemma application steps using exactly one lemma
 * are computed.
 *
 * In fact it is done by the class LemmaApplicationRealVisitorAll.
 * But an applications of implication (& equivalences) is possible, too.
 * So this is done before.
 * Equivalences are handeled by splitting them up into two implications.
 *
 * (Read the processor help for more information.)
 *
 * @author dickmeis
 * @version $Id$
 */

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LemmaApplication.*;
import aprove.verification.oldframework.Logic.Formulas.*;

class LemmaApplicationVisitorAll{

    protected Set<Formula> lemmas;

    /**
     * All possible applications of lemmas on a formula are computed
     *
     * @param formula The formula on which the lemmas are tried to apply on.
     * @param lemmas All the lemmas which will be tried for lemma application on the formula.
     * @return The outcome of every lemma application telling also which lemma was where applicated.
     */
    public static ArrayList<LemmaApplicationResult> apply(Formula formula, Set<Formula> lemmas) {
        ArrayList<LemmaApplicationResult> result;

        // apply implications and equivalences
        result = LemmaApplicationVisitorAll.applyImplications(formula, lemmas);

        ArrayList<LemmaApplicationResult> resultTemp;
        LemmaApplicationRealVisitorAll lemmaApplicationRealVisitorAll = new LemmaApplicationRealVisitorAll(lemmas, formula);

        // do most of the work
        resultTemp = formula.apply(lemmaApplicationRealVisitorAll);
        result.addAll(resultTemp);

        return result;
    }

    /**
     * For a set of lemmas all possible applications of the contained
     * implications (& equivalences) on a formula are computed.
     * Equivalences are handeled by splitting them up into two implications.
     *
     * @param formula The formula on which the implications (& equivalences) are tried to apply on.
     * @param lemmas  The set of lemmas from which the implications (& equivalences) are taken from
     *                  to apply on the formula
     * @return        The outcome of apllication telling also which lemma was where applicated.
     */
    protected static ArrayList<LemmaApplicationResult> applyImplications(Formula formula, Set<Formula> lemmas){
        ArrayList<LemmaApplicationResult> result;
        result = new ArrayList<LemmaApplicationResult>();
        LemmaApplicationResult res;
        AlgebraSubstitution substitution;
        Set<AlgebraVariable> formulaVars = formula.getAllVariables();
        Iterator<Formula> iterator = lemmas.iterator();

        while(iterator.hasNext()) {
            Formula lemma = iterator.next();

            // apply implications
            if (lemma instanceof Implication) {
                lemma.renameAllVars(formulaVars);
                Implication implLemma = (Implication) lemma;

                substitution = implLemma.getRight().matches(formula);

                if (substitution != null){
                    Position pos = Position.create();

                    res = new LemmaApplicationResult(
                            lemma, LemmaApplicationDirection.TOP, pos,
                            implLemma.getLeft().apply(substitution),
                            formula);
                    result.add(res);
                }
            }

            // apply equivalences
            if (lemma instanceof Equivalence) {
                lemma.renameAllVars(formulaVars);
                Equivalence equivLemma = (Equivalence) lemma;

                // first left to right
                substitution = equivLemma.getRight().matches(formula);

                if (substitution != null){
                    Position pos = Position.create();

                    res = new LemmaApplicationResult(
                            lemma, LemmaApplicationDirection.LEFT2RIGHT, pos,
                            equivLemma.getLeft().apply(substitution),
                            formula);
                    result.add(res);
                }

                // right to left
                substitution = equivLemma.getLeft().matches(formula);

                if (substitution != null){
                    Position pos = Position.create();

                    res = new LemmaApplicationResult(
                            lemma, LemmaApplicationDirection.RIGHT2LEFT, pos,
                            equivLemma.getRight().apply(substitution),
                            formula);
                    result.add(res);
                }
            }
        }

        return result;
    }

}

class LemmaApplicationRealVisitorAll implements FineFormulaVisitor<ArrayList<LemmaApplicationResult>>, CoarseGrainedTermVisitor<ArrayList<LemmaApplicationIntermediateResult>> {

    protected Set<Formula> lemmas;
    protected Set<AlgebraVariable> formulaVars;

    public static ArrayList<LemmaApplicationResult> apply(Formula formula, Set<Formula> lemmas) {
        LemmaApplicationRealVisitorAll lemmaApplicationRealVisitorAll = new LemmaApplicationRealVisitorAll(lemmas, formula);
        return formula.apply(lemmaApplicationRealVisitorAll);
    }

    protected LemmaApplicationRealVisitorAll(Set<Formula> lemmas, Formula formula) {
        this.lemmas = lemmas;
        this.formulaVars = formula.getAllVariables();
    }

    @Override
    public ArrayList<LemmaApplicationResult> caseEquivalence(Equivalence equivFormula) {
        ArrayList<LemmaApplicationResult> result = new ArrayList<LemmaApplicationResult>();
        LemmaApplicationResult res;

        this.applyAtThisLevel(equivFormula, this.lemmas, result);

        // recursive descent
        ArrayList<LemmaApplicationResult> subformulaApplicationResult;
        Formula left = equivFormula.getLeft();
        Formula right = equivFormula.getRight();

        subformulaApplicationResult = left.apply(this);

        for (LemmaApplicationResult application : subformulaApplicationResult) {
            if(application.getLemma() != null){
                ArrayList<Integer> al = new ArrayList<Integer>();
                al.add(0);
                Position pos = Position.create(al);
                pos.concatenateWith(application.getPosition());
                res = new LemmaApplicationResult(
                        application.getLemma(), application.getDirection(), pos,
                        Equivalence.create(application.getResult(),right),
                        equivFormula);
                result.add(res);
            }
        }

        subformulaApplicationResult = right.apply(this);

        for (LemmaApplicationResult application : subformulaApplicationResult) {
            if(application.getLemma() != null){
                ArrayList<Integer> al = new ArrayList<Integer>();
                al.add(1);
                Position pos = Position.create(al);
                pos.concatenateWith(application.getPosition());
                res = new LemmaApplicationResult(
                        application.getLemma(), application.getDirection(), pos,
                        Equivalence.create(left, application.getResult()),
                        equivFormula);
                result.add(res);
            }
        }

        return result;
    }

    @Override
    public ArrayList<LemmaApplicationResult> caseNot(Not notFormula) {
        ArrayList<LemmaApplicationResult> result = new ArrayList<LemmaApplicationResult>();
        LemmaApplicationResult t;
        ArrayList<LemmaApplicationResult> subformulaApplicationResult;
        Formula left = notFormula.getLeft();

        subformulaApplicationResult = left.apply(this);

        for (LemmaApplicationResult application : subformulaApplicationResult) {
            if(application.getLemma() != null){
                ArrayList<Integer> al = new ArrayList<Integer>();
                al.add(0);
                Position pos = Position.create(al);
                pos.concatenateWith(application.getPosition());
                t = new LemmaApplicationResult(
                        application.getLemma(), application.getDirection(), pos,
                        Not.create(application.getResult()),
                        notFormula);
                result.add(t);
            }
        }

        return result;
    }

    @Override
    public ArrayList<LemmaApplicationResult> caseImplication(Implication implFormula) {
        ArrayList<LemmaApplicationResult> result = new ArrayList<LemmaApplicationResult>();
        LemmaApplicationResult t;

        this.applyAtThisLevel(implFormula, this.lemmas, result);

        // recursive descent
        ArrayList<LemmaApplicationResult> subformulaApplicationResult;
        Formula left = implFormula.getLeft();
        Formula right = implFormula.getRight();

        subformulaApplicationResult = left.apply(this);

        for (LemmaApplicationResult application : subformulaApplicationResult) {
            if(application.getLemma() != null){
                ArrayList<Integer> al = new ArrayList<Integer>();
                al.add(0);
                Position pos = Position.create(al);
                pos.concatenateWith(application.getPosition());
                t = new LemmaApplicationResult(
                        application.getLemma(), application.getDirection(), pos,
                        Implication.create(application.getResult(),right),
                        implFormula);
                result.add(t);
            }
        }

        subformulaApplicationResult = right.apply(this);

        for (LemmaApplicationResult application : subformulaApplicationResult) {
            if(application.getLemma() != null){
                ArrayList<Integer> al = new ArrayList<Integer>();
                al.add(1);
                Position pos = Position.create(al);
                pos.concatenateWith(application.getPosition());
                t = new LemmaApplicationResult(
                        application.getLemma(), application.getDirection(), pos,
                        Implication.create(left, application.getResult()),
                        implFormula);
                result.add(t);
            }
        }

        return result;
    }

    @Override
    public ArrayList<LemmaApplicationResult> caseOr(Or orFormula) {
        ArrayList<LemmaApplicationResult> result = new ArrayList<LemmaApplicationResult>();
        LemmaApplicationResult t;

        this.applyAtThisLevel(orFormula, this.lemmas, result);

        // recursive descent
        ArrayList<LemmaApplicationResult> subformulaApplicationResult;
        Formula left = orFormula.getLeft();
        Formula right = orFormula.getRight();

        subformulaApplicationResult = left.apply(this);

        for (LemmaApplicationResult application : subformulaApplicationResult) {
            if(application.getLemma() != null){
                ArrayList<Integer> al = new ArrayList<Integer>();
                al.add(0);
                Position pos = Position.create(al);
                pos.concatenateWith(application.getPosition());
                t = new LemmaApplicationResult(
                        application.getLemma(), application.getDirection(), pos,
                        Or.create(application.getResult(),right),
                        orFormula);
                result.add(t);
            }
        }

        subformulaApplicationResult = right.apply(this);

        for (LemmaApplicationResult application : subformulaApplicationResult) {
            if(application.getLemma() != null){
                ArrayList<Integer> al = new ArrayList<Integer>();
                al.add(1);
                Position pos = Position.create(al);
                pos.concatenateWith(application.getPosition());
                t = new LemmaApplicationResult(
                        application.getLemma(), application.getDirection(), pos,
                        Or.create(left, application.getResult()),
                        orFormula);
                result.add(t);
            }
        }

        return result;
    }

    @Override
    public ArrayList<LemmaApplicationResult> caseAnd(And andFormula) {
        ArrayList<LemmaApplicationResult> result = new ArrayList<LemmaApplicationResult>();
        LemmaApplicationResult t;

        this.applyAtThisLevel(andFormula, this.lemmas, result);

        // recursive descent
        ArrayList<LemmaApplicationResult> subformulaApplicationResult;
        Formula left = andFormula.getLeft();
        Formula right = andFormula.getRight();

        subformulaApplicationResult = left.apply(this);

        for (LemmaApplicationResult application : subformulaApplicationResult) {
            if(application.getLemma() != null){
                ArrayList<Integer> al = new ArrayList<Integer>();
                al.add(0);
                Position pos = Position.create(al);
                pos.concatenateWith(application.getPosition());
                t = new LemmaApplicationResult(
                        application.getLemma(), application.getDirection(), pos,
                        And.create(application.getResult(),right),
                        andFormula);
                result.add(t);
            }
        }

        subformulaApplicationResult = right.apply(this);

        for (LemmaApplicationResult application : subformulaApplicationResult) {
            if(application.getLemma() != null){
                ArrayList<Integer> al = new ArrayList<Integer>();
                al.add(1);
                Position pos = Position.create(al);
                pos.concatenateWith(application.getPosition());
                t = new LemmaApplicationResult(
                        application.getLemma(), application.getDirection(), pos,
                        And.create(left, application.getResult()),
                        andFormula);
                result.add(t);
            }
        }

        return result;
    }

    @Override
    public ArrayList<LemmaApplicationResult> caseEquation(Equation eqFormula) {
        ArrayList<LemmaApplicationResult> result = new ArrayList<LemmaApplicationResult>();
        LemmaApplicationResult t;

        this.applyAtThisLevel(eqFormula, this.lemmas, result);

        // recursive descent
        ArrayList<LemmaApplicationIntermediateResult> subtermApplicationResult;
        AlgebraTerm left = eqFormula.getLeft();
        AlgebraTerm right = eqFormula.getRight();

        subtermApplicationResult = left.apply(this);

        for (LemmaApplicationIntermediateResult application : subtermApplicationResult) {
            if(application.getLemma() != null){
                ArrayList<Integer> al = new ArrayList<Integer>();
                al.add(0);
                Position pos = Position.create(al);
                pos.concatenateWith(application.getPosition());
                t = new LemmaApplicationResult(
                        application.getLemma(), application.getDirection(), pos,
                        Equation.create(application.getResult(),right),
                        eqFormula);
                result.add(t);
            }
        }

        subtermApplicationResult = right.apply(this);

        for (LemmaApplicationIntermediateResult application : subtermApplicationResult) {
            if(application.getLemma() != null){
                ArrayList<Integer> al = new ArrayList<Integer>();
                al.add(1);
                Position pos = Position.create(al);
                pos.concatenateWith(application.getPosition());
                t = new LemmaApplicationResult(
                        application.getLemma(), application.getDirection(), pos,
                        Equation.create(left, application.getResult()),
                        eqFormula);
                result.add(t);
            }
        }

        return result;
    }

    @Override
    public ArrayList<LemmaApplicationResult> caseTruthValue(FormulaTruthValue truthvalFormula) {
        ArrayList<LemmaApplicationResult> result = new ArrayList<LemmaApplicationResult>();
        LemmaApplicationResult t;
        t = new LemmaApplicationResult(
                null, null, Position.create(),
                truthvalFormula.deepcopy(),
                truthvalFormula);
        result.add(t);

        return result;
    }

    @Override
    public ArrayList<LemmaApplicationIntermediateResult> caseFunctionApp(AlgebraFunctionApplication f) {

        ArrayList<LemmaApplicationIntermediateResult> result = new ArrayList<LemmaApplicationIntermediateResult>();
        LemmaApplicationIntermediateResult t;

        Iterator<Formula> iterator = this.lemmas.iterator();

        while(iterator.hasNext()) {
            Formula lemma = iterator.next();
            if(lemma instanceof Equation) {
                // rename variables in lemma with fresh variables
                lemma.renameAllVars(this.formulaVars);
                Equation equation = (Equation)lemma;

                AlgebraSubstitution substitution=null;
                boolean matchFound=false;

                // first try to apply the lemma left to right
                try {
                    substitution = equation.getLeft().matches(f);
                    matchFound=true;
                    }
                catch(UnificationException e) {}

                if (matchFound){
                    t = new LemmaApplicationIntermediateResult(
                            lemma, LemmaApplicationDirection.LEFT2RIGHT,
                            Position.create(),
                            equation.getRight().apply(substitution));
                            // the result need not to be a function application itself
                            // as it can be a variable, too
                    result.add(t);
                }

                // then try to apply the lemma right to left
                matchFound=false;
                try {
                    substitution = equation.getRight().matches(f);
                    matchFound=true;
                }catch(UnificationException e) {}

                if (matchFound){
                    t = new LemmaApplicationIntermediateResult(
                        lemma, LemmaApplicationDirection.RIGHT2LEFT,
                        Position.create(),
                        equation.getLeft().apply(substitution));
                        // the result need not to be a function application itself
                        // as it can be a variable, too
                    result.add(t);
                }
            }
        }

        // then recursive descent
        List<AlgebraTerm> arguments = f.getArguments();
        Iterator<AlgebraTerm> argumentsIterator = arguments.iterator();
        AlgebraTerm argument;
        int position=0;

        while(argumentsIterator.hasNext()){
            argument = argumentsIterator.next();

            ArrayList<AlgebraTerm> firstArguments = new ArrayList<AlgebraTerm> ();
            for(int i=0; i<position; i++){
                firstArguments.add(arguments.get(i));
            }

            ArrayList<AlgebraTerm> lastArguments = new ArrayList<AlgebraTerm> ();
            for(int i=position+1; i<arguments.size(); i++){
                lastArguments.add(arguments.get(i));
            }

            ArrayList<LemmaApplicationIntermediateResult> subtermApplicationResult;
            subtermApplicationResult = argument.apply(this);

            for (LemmaApplicationIntermediateResult application : subtermApplicationResult) {
                ArrayList<AlgebraTerm> newArguments = new ArrayList<AlgebraTerm>();
                newArguments.addAll(firstArguments);
                newArguments.add(application.getResult());
                newArguments.addAll(lastArguments);
                if(application.getLemma() != null){
                    ArrayList<Integer> al = new ArrayList<Integer>();
                    al.add(position);
                    Position pos = Position.create(al);
                    pos.concatenateWith(application.getPosition());
                    t = new LemmaApplicationIntermediateResult(
                            application.getLemma(), application.getDirection(),
                            pos,
                            AlgebraFunctionApplication.create(f.getFunctionSymbol(), newArguments));
                    result.add(t);
                }
            }

            position++;
        }

        return result;
    }

    @Override
    public ArrayList<LemmaApplicationIntermediateResult> caseVariable(AlgebraVariable v) {
       ArrayList<LemmaApplicationIntermediateResult> result = new ArrayList<LemmaApplicationIntermediateResult>();
       LemmaApplicationIntermediateResult t;

       Iterator<Formula> iterator = this.lemmas.iterator();

       while(iterator.hasNext()) {
            Formula lemma = iterator.next();
            if(lemma instanceof Equation) {
                // rename variables in lemma with fresh variables
               lemma.renameAllVars(this.formulaVars);
                Equation equation = (Equation)lemma;

                AlgebraSubstitution substitution=null;
                boolean matchFound=false;

                // first try to apply the lemma left to right
                try {
                    substitution = equation.getLeft().matches(v);
                    matchFound=true;
                    }
                catch(UnificationException e) {}

                if (matchFound){
                   t = new LemmaApplicationIntermediateResult(
                           lemma, LemmaApplicationDirection.LEFT2RIGHT,
                           Position.create(),
                           equation.getRight().apply(substitution));
                   result.add(t);
                }

                // then try to apply the lemma right to left
                matchFound=false;
                try {
                    substitution = equation.getRight().matches(v);
                    matchFound=true;
                }catch(UnificationException e) {}

                if (matchFound){
                   t = new LemmaApplicationIntermediateResult(
                       lemma, LemmaApplicationDirection.RIGHT2LEFT,
                       Position.create(),
                       equation.getLeft().apply(substitution));
                   result.add(t);
                }
           }
       }

       return result;
    }

    protected void applyAtThisLevel(Formula formula, Set<Formula> lemmas, ArrayList<LemmaApplicationResult> result){
        LemmaApplicationResult res;
        Iterator<Formula> iterator = lemmas.iterator();

        while(iterator.hasNext()) {
            Formula lemma = iterator.next();
            // rename variables in lemma with fresh variables
            lemma.renameAllVars(this.formulaVars);

            // apply at top level
            AlgebraSubstitution substitution = lemma.matches(formula);

            if (substitution != null){
                Position pos = Position.create();

                res = new LemmaApplicationResult(
                        lemma, LemmaApplicationDirection.TOP, pos,
                        FormulaTruthValue.TRUE,
                        formula);
                result.add(res);
            }
        }
    }
}

