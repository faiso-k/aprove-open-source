package aprove.verification.dpframework.Orders.SAT.PLEncoders;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.Orders.SAT.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Binary Encoding for PL Formulas. i.e. if 3 functions are present, they will get a
 * subset of 00, 01, 10 as order.
 */
public class SimpleBinaryPLEncoder implements PLEncoder {

    private FormulaFactory<None> formulaFactory;
    private boolean allowQuasi;


    /**
     *
     * @param formulaFactory
     *   A factory for PL Subformulas.
     * @param allowQuasi
     *   Specifies wheter to allow unstrict orders.
     */
    public SimpleBinaryPLEncoder(FormulaFactory<None> formulaFactory, boolean allowQuasi) {
        this.formulaFactory = formulaFactory;
        this.allowQuasi = allowQuasi;
    }


    /**
     *
     * @param poFormula
     *   The PO-Formula to encode to PL.
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

        // Calculates #bits needed for binary encoding, and possible num of Functions.
        // We have to use +1 if we want to restrict 0 to be bottom-only.
        int numBits = numVars > 1 ? 32 - Integer.numberOfLeadingZeros(numVars) : 1;
        int possibleNumVars = AProVEMath.power(2, numBits);

        Map<FunctionSymbol, Variable<None>[]> varMap = new LinkedHashMap<FunctionSymbol, Variable<None>[]>();
        Map<FunctionSymbol, NotFormula<None>[]> notMap = new LinkedHashMap<FunctionSymbol, NotFormula<None>[]>();
        for (FunctionSymbol f : ve.vars) {
            Variable<None>[] fVars = new Variable[numBits];
            NotFormula<None>[] fNots = new NotFormula[numBits];

            // Creation of the f_i's and their negations.
            for (int i = 0; i < numBits; i++) {
                fVars[i] = this.formulaFactory.buildVariable();
                fNots[i] = (NotFormula<None>) this.formulaFactory.buildNot(fVars[i]);
            }
            varMap.put(f, fVars);
            notMap.put(f, fNots);

            // Domain Restriction
            // Prohibit Encoding range beyond scope of numVars
            // Seems to increase speed a bit.
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            for (int i=numVars; i<possibleNumVars; i++) {
                // Prohibit binary encoding of i to happen.
                // Do this Max-Term style.
                for (int j=0; j< numBits; j++) {
                    if ((i & (1 << j)) != 0) {
                        dArgs.add(fNots[j]);
                    } else {
                        dArgs.add(fVars[j]);
                    }
                }
                cArgs.add(this.formulaFactory.buildOr(dArgs));
                dArgs.clear();
            }

        }


        for (Map.Entry<FactBot, Variable<None>> entry : ve.bots.entrySet()) {
            // Encode Bottom constraints
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
            /*// EXPERIMENTAL:
            // Ensure that just one bottom var the most is set.
            // Do this by disjuncting the negations of every pair of bottom variables...
            for (i = 0; i < botVars.length; i++) {
                for (int j=i; j < botVars.length; j++) {
                    cArgs.add(this.formulaFactory.buildOr(botNots[i], botNots[j]));
                }
            }*/

        }
        for (Map.Entry<FactSucc, Variable<None>> entry : ve.succs.entrySet()) {
            // Encode Successor constraints
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
            // Encode Equality Constraints
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

    private void encodeEqual(int i, Variable<None>[] fVars, NotFormula<None>[] fNots, Variable<None>[] gVars, NotFormula<None>[] gNots, Variable<None> var, NotFormula<None> not, List<Formula<None>> cArgs) {

        if (i+1 == fVars.length) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
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
            Variable<None> newVar = this.formulaFactory.buildVariable();
            NotFormula<None> newNot = (NotFormula<None>) this.formulaFactory.buildNot(newVar);
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
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
            this.encodeEqual(i+1, fVars, fNots, gVars, gNots, newVar, newNot, cArgs);
        }
/*
        List<Formula> dArgs = new ArrayList<Formula>();
        dArgs.add(var);

        Variable e = null, eprev = null;
        Formula ne=null, neprev= null;

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
   //         cArgs.add(this.formulaFactory.buildOr(not, ne));

            eprev = e;
            neprev  = ne;
        }
        // For testing on at least one error.
        cArgs.add(this.formulaFactory.buildOr(var,e));
        cArgs.add(this.formulaFactory.buildOr(not,ne));



    */


    }

    /**
     * Succesor constraints are solved by coding a variable (var) to be true iff rep(f) > rep(g).
     */
    private void encodeSucc(int i, Variable<None>[] fVars, NotFormula<None>[] fNots, Variable<None>[] gVars, NotFormula<None>[] gNots, Variable<None> var, NotFormula<None> not, List<Formula<None>> cArgs) {
     /*   if (i+1 == fVars.length) {
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
            NotFormula newNot = (NotFormula) this.formulaFactory.buildNot(newVar);
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
        }*/

        // Optimized Versions: All Clauses consist of no more than 3 literals.
        // This is achieved by having Match variables for each position where a match has happened
        // or not, and dealing with them as neccesary
        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        dArgs.add(not);

        Variable<None> localMatch = null;
        Formula<None> notLocalMatch = null;
        Variable<None> localMatchPrevious = null;
        Formula<None> notLocalMatchPrevious = null;
        for (int j=0; j < fVars.length; j++) {

            localMatch = this.formulaFactory.buildVariable();
            notLocalMatch = this.formulaFactory.buildNot(localMatch);
            // We have a match if fj is set, but gj is not.
            dArgs.clear();
            dArgs.add(localMatch);
            dArgs.add(fNots[j]);
            dArgs.add(gVars[j]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            // We don't have a match (anymore) if fj is unset and gj is set.
            cArgs.add(this.formulaFactory.buildOr(notLocalMatch, fVars[j], gNots[j]));
            // If fj is set or gj is unset, keep match.
            // But we don't have a match if neither we had one nor fj is set. Same with gj
            if (j>0) {
                cArgs.add(this.formulaFactory.buildOr(localMatch,notLocalMatchPrevious,fNots[j]));
                cArgs.add(this.formulaFactory.buildOr(notLocalMatch,localMatchPrevious,fVars[j]));
                cArgs.add(this.formulaFactory.buildOr(localMatch,notLocalMatchPrevious,gVars[j]));
                cArgs.add(this.formulaFactory.buildOr(notLocalMatch,localMatchPrevious,gNots[j]));
            } else {
                cArgs.add(this.formulaFactory.buildOr(notLocalMatch,gNots[j]));
                cArgs.add(this.formulaFactory.buildOr(notLocalMatch,fVars[j]));
            }


            localMatchPrevious = localMatch;
            notLocalMatchPrevious = notLocalMatch;
        }

        // For testing on a match:
        cArgs.add(this.formulaFactory.buildOr(not, localMatch));
        cArgs.add(this.formulaFactory.buildOr(var, notLocalMatch));

    }

    private void encodeBot(int i, Variable<None>[] vars, NotFormula<None>[] nots, Variable<None> var, NotFormula<None> not, List<Formula<None>> cArgs) {

        // This Version seems to provide about the same / a little better performance in binary encoding.
        if (i+1 == vars.length) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            dArgs.add(var);
            dArgs.add(vars[i]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(not);
            dArgs.add(nots[i]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
        } else {
            Variable<None> newVar = this.formulaFactory.buildVariable();
            NotFormula<None> newNot = (NotFormula<None>) this.formulaFactory.buildNot(newVar);
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            dArgs.add(not);
            dArgs.add(nots[i]);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(not);
            dArgs.add(newVar);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            dArgs.clear();
            dArgs.add(var);
            dArgs.add(vars[i]);
            dArgs.add(newNot);
            cArgs.add(this.formulaFactory.buildOr(dArgs));
            this.encodeBot(i+1, vars, nots, newVar, newNot, cArgs);
        }

        // New version: Seems to be slower in binary encoding if
        // Domain restriction is used.
        // If bottom is set, force every Variable to be 0.
        /*for (int j=0; j<vars.length; j++ ) {
            List<Formula> dArgs = new ArrayList<Formula>();
            dArgs.add(not);
            dArgs.add(nots[j]);
            cArgs.add(formulaFactory.buildOr(dArgs));
        }*/
    }



}
