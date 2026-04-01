package aprove.verification.dpframework.Orders.SAT.PLEncoders;


import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.Orders.SAT.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;


/**
 * Provides a unary order for PO-to-PL Encoding.
 * I.e. if f contains 4 function symbols, they will be encoded 000, 001, 011, 111
 * @author Patrick Kabasci
 *
 */
public class SimpleUnaryPLEncoder implements PLEncoder {

    private FormulaFactory<None> formulaFactory;
    private boolean allowQuasi;


    /**
     *
     * @param formulaFactory
     *   A factory for PL Subformulas.
     * @param allowQuasi
     *   Specifies wheter to allow unstrict orders.
     */
    public SimpleUnaryPLEncoder(FormulaFactory<None> formulaFactory, boolean allowQuasi) {
        this.formulaFactory = formulaFactory;
        this.allowQuasi = allowQuasi;
    }


    /**
     *
     * @param poFormula
     *   The PO-Formula<None> to encode to PL.
     * @param aborter
     *   An aborter instance to signal termination.
     *
     */
    @Override
    public Formula<None> toPropositionalFormula(POFormula poFormula, Abortion aborter) throws AbortionException {
        Formula<None> formula = poFormula.getFormula();

        // Collects all Symbols actually used in any constraints.
        CollectVarsEdges ve = new CollectVarsEdges(poFormula.getPOConstraints());
        formula.apply(ve);
        int numVars = ve.vars.size();

        // The encoded PL Subformulae
        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();



        // Generate Function Symbols and for convenience their negations.
        Map<FunctionSymbol, Variable<None>[]> varMap = new LinkedHashMap<FunctionSymbol, Variable<None>[]>();
        Map<FunctionSymbol, NotFormula<None>[]> notMap = new LinkedHashMap<FunctionSymbol, NotFormula<None>[]>();
        for (FunctionSymbol f : ve.vars) {
            Variable<None>[] fVars = new Variable[numVars - 1];
            NotFormula<None>[] fNots = new NotFormula[numVars - 1];

            // Creation of the f_i's and their negations.
            for (int i = 0; i < numVars - 1; i++) {
                fVars[i] = this.formulaFactory.buildVariable();
                fNots[i] = (NotFormula<None>) this.formulaFactory.buildNot(fVars[i]);
            }
            varMap.put(f, fVars);
            notMap.put(f, fNots);

            //Insist on order, that is a 1 can only be folloed by ones.
            for(int i = 1; i < numVars - 1; i++) {
                List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                dArgs.add(fVars[i-1]);
                dArgs.add(fNots[i]);
                cArgs.add(this.formulaFactory.buildOr(dArgs));
            }

        }


        for (Map.Entry<FactBot, Variable<None>> entry : ve.bots.entrySet()) {
            aborter.checkAbortion();
            FactBot bot = entry.getKey();
            FunctionSymbol f = bot.getFunctionSymbol();
            Variable<None>[] fVars = varMap.get(f);
            NotFormula<None>[] fNots = notMap.get(f);
            Variable<None> var = entry.getValue();
            NotFormula<None> not = (NotFormula<None>) this.formulaFactory.buildNot(var);
            this.encodeBot(0, fVars, fNots, var, not, cArgs);
        }

        if (!this.allowQuasi) {
            Variable<None>[] botVars = new Variable[ve.bots.keySet().size()];
            int i = 0;

            // Insisting on having no more than one bottom variable: Building bottom Vars
            for (Variable<None> botVar : ve.bots.values()) {
                botVars[i] = botVar;
                i++;
            }
            NotFormula<None>[] botNots = new NotFormula[botVars.length];
            for (i = 0; i < botVars.length; i++) {
                botNots[i] = (NotFormula<None>) this.formulaFactory.buildNot(botVars[i]);
            }
            // Not yet in CNF, if we desire to optimize by hand.
            // Ensure that for each bottom variable, that variable is unset or
            // all other bottom variables are unset.
            for (i = 0; i < botVars.length; i++) {
                aborter.checkAbortion();
                List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                dArgs.add(botNots[i]);
                List<Formula<None>> bArgs = new ArrayList<Formula<None>>();
                for (int j = 0; j < i; j++) {
                    bArgs.add(botNots[j]);
                }
                for (int j = i+1; j < botVars.length; j++) {
                    bArgs.add(botNots[j]);
                }
                dArgs.add(this.formulaFactory.buildAnd(bArgs));
                cArgs.add(this.formulaFactory.buildOr(dArgs));
            }
        }
        for (Map.Entry<FactSucc, Variable<None>> entry : ve.succs.entrySet()) {
            aborter.checkAbortion();
            FactSucc succ = entry.getKey();
            FunctionSymbol f = succ.getLeft();
            FunctionSymbol g = succ.getRight();
            Variable<None>[] fVars = varMap.get(f);
            NotFormula<None>[] fNots = notMap.get(f);
            Variable<None>[] gVars = varMap.get(g);
            NotFormula<None>[] gNots = notMap.get(g);
            Variable<None> var = entry.getValue();
            NotFormula<None> not = (NotFormula<None>) this.formulaFactory.buildNot(var);
            this.encodeSucc(0, fVars, fNots, gVars, gNots, var, not, cArgs);
        }
        for (Map.Entry<FactEqual, Variable<None>> entry : ve.equals.entrySet()) {
            aborter.checkAbortion();
            FactEqual equal = entry.getKey();
            FunctionSymbol f = equal.getLeft();
            FunctionSymbol g = equal.getRight();
            Variable<None>[] fVars = varMap.get(f);
            NotFormula<None>[] fNots = notMap.get(f);
            Variable<None>[] gVars = varMap.get(g);
            NotFormula<None>[] gNots = notMap.get(g);
            Variable<None> var = entry.getValue();
            NotFormula<None> not = (NotFormula<None>) this.formulaFactory.buildNot(var);
            this.encodeEqual(0, fVars, fNots, gVars, gNots, var, not, cArgs);
        }
        cArgs.add(formula);
        return this.formulaFactory.buildAnd(cArgs);
    }


    /**
     * Encodes an equality constraint to PL
     * @param i Recursion Variable; set to 0 on first call
     * @param fVars Encoding variables of the first Function symbol
     * @param fNots Negations of the vars in fVars
     * @param gVars Encoding variables of the second Function symbol
     * @param gNots Negations of the vars in gVars
     * @param var   Root truth varable of this constraint
     * @param not   Negation of var
     * @param cArgs CNF clause collection for the SAT solver
     */
    private void encodeEqual(int i, Variable<None>[] fVars, NotFormula<None>[] fNots, Variable<None>[] gVars, NotFormula<None>[] gNots, Variable<None> var, NotFormula<None> not, List<Formula<None>> cArgs) {
        /*//The implementation used for binary encoding
        if (i+1 == fVars.length) {
            List<Formula> dArgs = new ArrayList<Formula>();
            dArgs.add(not);
            dArgs.add(fNots[i]);
            dArgs.add(gVars[i]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(not);
            dArgs.add(fVars[i]);
            dArgs.add(gNots[i]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(var);
            dArgs.add(fVars[i]);
            dArgs.add(gVars[i]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(var);
            dArgs.add(fNots[i]);
            dArgs.add(gNots[i]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
        } else {
            Variable newVar = this.formulaFactory.buildVariable();
            NotFormula<None> newNot = (NotFormula) this.formulaFactory.buildNot(newVar);
            List<Formula> dArgs = new ArrayList<Formula>();
            dArgs.add(not);
            dArgs.add(fVars[i]);
            dArgs.add(gNots[i]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(not);
            dArgs.add(fNots[i]);
            dArgs.add(gVars[i]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(not);
            dArgs.add(newVar);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(var);
            dArgs.add(fVars[i]);
            dArgs.add(gVars[i]);
            dArgs.add(newNot);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(var);
            dArgs.add(fNots[i]);
            dArgs.add(gNots[i]);
            dArgs.add(newNot);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            encodeEqual(i+1, fVars, fNots, gVars, gNots, newVar, newNot, cArgs);
        }
        */


        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        dArgs.add(var);

        Variable<None> e = null, eprev = null;
        Formula<None> ne, neprev= null;

        for (int j=0; j < fVars.length; j++) {

            e = this.formulaFactory.buildVariable();
            ne = this.formulaFactory.buildNot(e);
            // We have a mismatch if fj is set, but gj is not.
            cArgs.add(this.formulaFactory.buildOr(e, fNots[j], gVars[j]));
            // We have a mismatch if gj is set, but fj is not.
            cArgs.add(this.formulaFactory.buildOr(e, fVars[j], gNots[j]));
            // We have a mismatch if we have had a mismatch before.
            if (j>0) {
                cArgs.add(this.formulaFactory.buildOr(e, neprev));
            }
            // We don't have a mismatch if fj and gj are unset, and there was no error before.
            dArgs.clear();
            dArgs.add(ne);
            dArgs.add(fVars[j]);
            dArgs.add(gVars[j]);
            if (j>0) {
                dArgs.add(eprev);
            }
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            // We don't have a mismatch if fj and gj are set, and we have not had an error before.
            dArgs.clear();
            dArgs.add(ne);
            dArgs.add(fNots[j]);
            dArgs.add(gNots[j]);
            if (j>0) {
                dArgs.add(eprev);
            }
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            // If we have a local mismatch, we also have a global mismatch.
            cArgs.add(this.formulaFactory.buildOr(not, ne));

            eprev = e;
            neprev  = ne;
        }
        // For testing on at least one error.
        cArgs.add(this.formulaFactory.buildOr(var,e));

    }

    /**
     * Encodes a succession constraint to PL
     * @param i Recursion Variable; set to 0 on first call
     * @param fVars Encoding variables of the first Function symbol
     * @param fNots Negations of the vars in fVars
     * @param gVars Encoding variables of the second Function symbol
     * @param gNots Negations of the vars in gVars
     * @param var   Root truth varable of this constraint
     * @param not   Negation of var
     * @param cArgs CNF clause collection for the SAT solver
     */
    // f > g <=> exists bit i of f > bit i of g
    private void encodeSucc(int i, Variable<None>[] fVars, NotFormula<None>[] fNots, Variable<None>[] gVars, NotFormula<None>[] gNots, Variable<None> var, NotFormula<None> not, List<Formula<None>> cArgs) {
       /* if (i+1 == fVars.length) {
            List<Formula> dArgs = new ArrayList<Formula>();
            dArgs.add(not);
            dArgs.add(fVars[i]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(not);
            dArgs.add(fNots[i]);
            dArgs.add(gNots[i]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(var);
            dArgs.add(fNots[i]);
            dArgs.add(gVars[i]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
        } else {
            Variable newVar = this.formulaFactory.buildVariable();
            NotFormula<None> newNot = (NotFormula) this.formulaFactory.buildNot(newVar);
            List<Formula> dArgs = new ArrayList<Formula>();
            dArgs.add(not);
            dArgs.add(fVars[i]);
            dArgs.add(gNots[i]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(var);
            dArgs.add(fNots[i]);
            dArgs.add(gVars[i]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(not);
            dArgs.add(fVars[i]);
            dArgs.add(gVars[i]);
            dArgs.add(newVar);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(not);
            dArgs.add(fNots[i]);
            dArgs.add(gNots[i]);
            dArgs.add(newVar);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(var);
            dArgs.add(fNots[i]);
            dArgs.add(gNots[i]);
            dArgs.add(newNot);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(var);
            dArgs.add(fVars[i]);
            dArgs.add(gVars[i]);
            dArgs.add(newNot);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            encodeSucc(i+1, fVars, fNots, gVars, gNots, newVar, newNot, cArgs);
        }
        */
        /*
        // Naive Implementation (Deslate performance)
         List<Formula> dArgs = new ArrayList<Formula>();
        for (int j=0; j<fVars.length; j++) {
            dArgs.add(this.formulaFactory.buildAnd(gNots[j], fVars[j]));
        }

        Formula<None> trueForm;
        trueForm = this.formulaFactory.buildAnd(this.formulaFactory.buildOr(dArgs), var);
        cArgs.add(this.formulaFactory.buildOr(not, trueForm));
         */

        // A little more sophisticated: Generate Match variables for
        // each symbol. If any bit of g < that bit of f, set corresp. match.
        // If any match is set, mark as satisfyable. Uses only implications.
        // Big performance increase (~2/3) toward naive implementation.
        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        dArgs.add(not);

        Variable<None> e = null;
        Formula<None> ne = null;
        Variable<None> eprev = null;
        Formula<None> neprev = null;
        for (int j=0; j < fVars.length; j++) {

            e = this.formulaFactory.buildVariable();
            ne = this.formulaFactory.buildNot(e);
            // We can have a match if fj is set, but gj is not, or if we ha had a match before.
            dArgs.clear();
            dArgs.add(e);
            dArgs.add(fNots[j]);
            dArgs.add(gVars[j]);
            if (j>0) {
                dArgs.add(neprev);
            }
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            // We don't have a match if fj is unset, and there was no match the Term before.
            if (j>0) {
                cArgs.add(this.formulaFactory.buildOr(ne, fVars[j], eprev));
            } else {
                cArgs.add(this.formulaFactory.buildOr(ne, fVars[j]));
            }
            // We don't have a match if gj is set.
            cArgs.add(this.formulaFactory.buildOr(ne, gNots[j]));
            // If we have a local match, we also have a global match.
            cArgs.add(this.formulaFactory.buildOr(var, ne));


            eprev = e;
            neprev = ne;
        }

        // For testing on a match:
        cArgs.add(this.formulaFactory.buildOr(not, e));

        /*

        List<Formula> dArgs = new ArrayList<Formula>();
        dArgs.add(not);

        Variable e = null;
        Formula<None> ne = null;
        Variable eprev = null;
        Formula<None> neprev = null;
        for (int j=0; j < fVars.length; j++) {

            e = this.formulaFactory.buildVariable();
            ne = this.formulaFactory.buildNot(e);
            // We have a match if fj is set, but gj is not.
            dArgs.clear();
            dArgs.add(e);
            dArgs.add(fNots[j]);
            dArgs.add(gVars[j]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            // We don't have a match (anymore) if fj is unset and gj is set.
            cArgs.add(this.formulaFactory.buildOr(ne, fVars[j], gNots[j]));
            // If fj is set or gj is unset, keep match.
            // But we don't have a match if neither we had one nor fj is set. Same with gj
            if (j>0) {
                cArgs.add(this.formulaFactory.buildOr(e,neprev,fNots[j]));
                cArgs.add(this.formulaFactory.buildOr(ne,eprev,fVars[j]));
                cArgs.add(this.formulaFactory.buildOr(e,neprev,gVars[j]));
                cArgs.add(this.formulaFactory.buildOr(ne,eprev,gNots[j]));
            } else {
                cArgs.add(this.formulaFactory.buildOr(ne,gNots[j]));
                cArgs.add(this.formulaFactory.buildOr(ne,fVars[j]));
            }


            eprev = e;
            neprev = ne;
        }

        // For testing on a match:
        cArgs.add(this.formulaFactory.buildOr(not, e));
        cArgs.add(this.formulaFactory.buildOr(var, ne));
        */
    }


    /**
     * Encodes a bottom constraint to PL
     * @param i Recursion Variable; set to 0 on first call
     * @param vars Encoding variables of the Function symbol
     * @param ots Negations of the vars in fVars
     * @param var   Root
     * @param not   Negation of var
     * @param cArgs CNF clause collection for the SAT solver
     */
    private void encodeBot(int i, Variable<None>[] vars, NotFormula<None>[] nots, Variable<None> var, NotFormula<None> not, List<Formula<None>> cArgs) {
        // If bottom is set, force all Variable<None>s to be 0. Keep
        // the for loop. It is cruical, otherwise performance will drop.
        // (allthough a check for the last bit would otherwise suffice)
        for (int j=0; j<vars.length; j++ ) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            dArgs.add(not);
            dArgs.add(nots[j]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
        }


    }

}