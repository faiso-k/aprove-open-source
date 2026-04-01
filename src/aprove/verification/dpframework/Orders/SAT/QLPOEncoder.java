package aprove.verification.dpframework.Orders.SAT;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class QLPOEncoder extends LPOEncoder {

    private final static int BLOWUP_THRESHOLD = 6;

    /**
     * Cache already computed values of encodeQLPOEqual
     * to avoid exponential blowup.
     */
    private Map<Triple<Pair<Integer, TRSFunctionApplication>, Pair<Integer, TRSFunctionApplication>, ValueCache<None>>, Formula<None>> knownQLPOEqual = new HashMap<Triple<Pair<Integer, TRSFunctionApplication>, Pair<Integer, TRSFunctionApplication>, ValueCache<None>>, Formula<None>>();
    /**
     * Cache already computed values of encodeQLPOLex
     * to avoid exponential blowup.
     */
    private Map<Triple<Pair<Integer, TRSFunctionApplication>, Pair<Integer, TRSFunctionApplication>, ValueCache<None>>, Formula<None>> knownQLPOLex = new HashMap<Triple<Pair<Integer, TRSFunctionApplication>, Pair<Integer, TRSFunctionApplication>, ValueCache<None>>, Formula<None>>();

    public QLPOEncoder(FormulaFactory<None> formulaFactory) {
        this(formulaFactory, 0);
    }

    public QLPOEncoder(FormulaFactory<None> formulaFactory, int restriction) {
        super(formulaFactory, restriction);
        this.tryStatus = false;
        this.allowQuasi = true;
    }

    @Override
    protected Formula<None> encodeGRNonCollapsing(TRSTerm s, TRSFunctionApplication sApp, TRSTerm t, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        Formula<None> formula = this.encodeDisjunction(sApp, t, OrderRelation.GE, knownValues);
        if (formula == this.ONE) {
            return this.ONE;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(formula);
        FunctionSymbol f = sApp.getRootSymbol();
        FunctionSymbol g = tApp.getRootSymbol();
        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
        if (!f.equals(g)) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            Variable<None> varFSuccG = this.factFactory.getVarSucc(f,g);
            Formula<None> eVarFSuccG = varFSuccG.evaluate(knownValues);
            Variable<None> varFEqualG = this.factFactory.getVarEqual(f,g);
            Formula<None> eVarFEqualG = varFEqualG.evaluate(knownValues);
            if (eVarFSuccG != this.ZERO && eVarFEqualG != this.ONE) {
                dArgs.add(eVarFSuccG);
            }
            if (eVarFSuccG != this.ONE && eVarFEqualG != this.ZERO) {
                ValueCache<None> newValues = knownValues.copy();
                NotFormula<None> notFSuccG = this.factFactory.getNotSucc(f, g);
                newValues.update(notFSuccG);
                newValues.update(varFEqualG);
                List<Formula<None>> bArgs = new ArrayList<Formula<None>>();
                bArgs.add(notFSuccG.evaluate(knownValues));
                bArgs.add(eVarFEqualG);
                bArgs.add(this.encodeQArgCompare(sApp, tApp, newValues));
                dArgs.add(this.formulaFactory.buildAnd(bArgs));
            }
            formula = this.formulaFactory.buildOr(dArgs);
        } else {
            formula = this.encodeArgCompare(sApp, tApp, knownValues);
        }
        if (formula != this.ZERO) {
            cArgs.add(formula);
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(formula);
            cArgs.add(this.encodeConjunction(s, tApp, OrderRelation.GR, newValues));
            args.add(this.formulaFactory.buildAnd(cArgs));
        }
        return this.formulaFactory.buildOr(args);
    }

    protected Formula<None> encodeQArgCompare(TRSFunctionApplication sApp, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        if (sApp.getRootSymbol().getArity() < QLPOEncoder.BLOWUP_THRESHOLD && tApp.getRootSymbol().getArity() < QLPOEncoder.BLOWUP_THRESHOLD) {
            return this.encodeQLPOLexSmall(0, sApp, 0, tApp, knownValues);
        }
        return this.encodeQLPOLex(0, sApp, 0, tApp, knownValues);
    }

    protected Formula<None> encodeQLPOLexSmall(int i, TRSFunctionApplication sApp, int j, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        if (aprove.Globals.DEBUG_NOWONDER) {
            System.err.println(sApp+"/"+i+" LexQLPO "+tApp+"/"+j);
        }
        FunctionSymbol f = sApp.getRootSymbol();
        FunctionSymbol g = tApp.getRootSymbol();
        int fArity = f.getArity();
        int gArity = g.getArity();
        if (!(i < fArity)) {
            return this.ZERO;
        }
        if (!(j < gArity)) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            for (int k = i; k < fArity; k++) {
                dArgs.add(this.factFactory.getVarArg(f, k).evaluate(knownValues));
            }
            return this.formulaFactory.buildOr(dArgs);
        }
        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        NotFormula<None> notFArgI = this.factFactory.getNotArg(f, i);
        Formula<None> eNotFArgI = notFArgI.evaluate(knownValues);
        if (eNotFArgI != this.ZERO) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(notFArgI);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eNotFArgI);
            cArgs.add(this.encodeQLPOLexSmall(i+1, sApp, j, tApp, newValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return formula;
            }
            dArgs.add(formula);
        }
        Variable<None> varFArgI = this.factFactory.getVarArg(f, i);
        Formula<None> eVarFArgI = varFArgI.evaluate(knownValues);
        NotFormula<None> notGArgJ = this.factFactory.getNotArg(g, j);
        Formula<None> eNotGArgJ = notGArgJ.evaluate(knownValues);
        if (eVarFArgI != this.ZERO && eNotGArgJ != this.ZERO) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(varFArgI);
            newValues.update(notGArgJ);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarFArgI);
            cArgs.add(eNotGArgJ);
            cArgs.add(this.encodeQLPOLexSmall(i, sApp, j+1, tApp, newValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return formula;
            }
            dArgs.add(formula);
        }
        Variable<None> varGArgJ = this.factFactory.getVarArg(g, j);
        Formula<None> eVarGArgJ = varGArgJ.evaluate(knownValues);
        if (eVarFArgI != this.ZERO && eVarGArgJ != this.ZERO) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(varFArgI);
            newValues.update(varGArgJ);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarFArgI);
            cArgs.add(eVarGArgJ);
            List<Formula<None>> eArgs = new ArrayList<Formula<None>>();
            List<Formula<None>> bArgs = new ArrayList<Formula<None>>();
            TRSTerm si = sApp.getArgument(i);
            TRSTerm tj = tApp.getArgument(j);
            bArgs.add(this.encodeGENGR(si, tj, newValues));
            bArgs.add(this.encodeQLPOLexSmall(i+1, sApp, j+1, tApp, newValues));
            Formula<None> formula = this.formulaFactory.buildAnd(bArgs);
            eArgs.add(formula);
            if (formula != this.ONE) {
                eArgs.add(this.encodeGR(si, tj, newValues));
            }
            cArgs.add(this.formulaFactory.buildOr(eArgs));
            formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return formula;
            }
            dArgs.add(formula);
        }
        return this.formulaFactory.buildOr(dArgs);
    }

    protected Formula<None> encodeQLPOLex(int i, TRSFunctionApplication sApp, int j, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        if (aprove.Globals.DEBUG_NOWONDER) {
            System.err.println(sApp+"/"+i+" LexQLPO "+tApp+"/"+j);
        }
        Triple<Pair<Integer, TRSFunctionApplication>, Pair<Integer, TRSFunctionApplication>, ValueCache<None>> id = new Triple<Pair<Integer, TRSFunctionApplication>, Pair<Integer, TRSFunctionApplication>, ValueCache<None>>(new Pair<Integer, TRSFunctionApplication>(i, sApp), new Pair<Integer, TRSFunctionApplication>(j, tApp), knownValues);
        Formula<None> knownResult = this.knownQLPOLex.get(id);
        if (knownResult != null) {
            if (aprove.Globals.DEBUG_NOWONDER) {
                System.err.println("REUSED CACHE");
            }
            return knownResult;
        }
        FunctionSymbol f = sApp.getRootSymbol();
        FunctionSymbol g = tApp.getRootSymbol();
        int fArity = f.getArity();
        int gArity = g.getArity();
        if (!(i < fArity)) {
            return this.updateQLPOLex(id, this.ZERO);
        }
        if (!(j < gArity)) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            for (int k = i; k < fArity; k++) {
                dArgs.add(this.factFactory.getVarArg(f, k).evaluate(knownValues));
            }
            return this.updateQLPOLex(id, this.formulaFactory.buildOr(dArgs));
        }
        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        NotFormula<None> notFArgI = this.factFactory.getNotArg(f, i);
        Formula<None> eNotFArgI = notFArgI.evaluate(knownValues);
        if (eNotFArgI != this.ZERO) {
            //ValueCache newValues = knownValues.copy();
            //newValues.update(notFArgI);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eNotFArgI);
            cArgs.add(this.encodeQLPOLex(i+1, sApp, j, tApp, knownValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return this.updateQLPOLex(id, formula);
            }
            dArgs.add(formula);
        }
        Variable<None> varFArgI = this.factFactory.getVarArg(f, i);
        Formula<None> eVarFArgI = varFArgI.evaluate(knownValues);
        NotFormula<None> notGArgJ = this.factFactory.getNotArg(g, j);
        Formula<None> eNotGArgJ = notGArgJ.evaluate(knownValues);
        if (eVarFArgI != this.ZERO && eNotGArgJ != this.ZERO) {
            //ValueCache newValues = knownValues.copy();
            //newValues.update(varFArgI);
            //newValues.update(notGArgJ);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarFArgI);
            cArgs.add(eNotGArgJ);
            cArgs.add(this.encodeQLPOLex(i, sApp, j+1, tApp, knownValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return this.updateQLPOLex(id, formula);
            }
            dArgs.add(formula);
        }
        Variable<None> varGArgJ = this.factFactory.getVarArg(g, j);
        Formula<None> eVarGArgJ = varGArgJ.evaluate(knownValues);
        if (eVarFArgI != this.ZERO && eVarGArgJ != this.ZERO) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(varFArgI);
            newValues.update(varGArgJ);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarFArgI);
            cArgs.add(eVarGArgJ);
            List<Formula<None>> eArgs = new ArrayList<Formula<None>>();
            List<Formula<None>> bArgs = new ArrayList<Formula<None>>();
            TRSTerm si = sApp.getArgument(i);
            TRSTerm tj = tApp.getArgument(j);
            bArgs.add(this.encodeGENGR(si, tj, newValues));
            bArgs.add(this.encodeQLPOLex(i+1, sApp, j+1, tApp, knownValues));
            Formula<None> formula = this.formulaFactory.buildAnd(bArgs);
            eArgs.add(formula);
            if (formula != this.ONE) {
                eArgs.add(this.encodeGR(si, tj, newValues));
            }
            cArgs.add(this.formulaFactory.buildOr(eArgs));
            formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return this.updateQLPOLex(id, formula);
            }
            dArgs.add(formula);
        }
        return this.updateQLPOLex(id, this.formulaFactory.buildOr(dArgs));
    }

    private Formula<None> updateQLPOLex(Triple<Pair<Integer, TRSFunctionApplication>, Pair<Integer, TRSFunctionApplication>, ValueCache<None>> id, Formula<None> formula) {
        if (aprove.Globals.DEBUG_NOWONDER) {
            System.err.println("Storing in Lex cache: "+id);
        }
        this.knownQLPOLex.put(id, formula);
        return formula;
    }

    @Override
    public AfsOrder getOrder(Set<Variable<None>> knownTrue, Afs afs) {
        Map<FunctionSymbol, FunctionSymbol> symbolMap = afs.getSymbolMap(this.sig);
        Qoset<FunctionSymbol> qoset = Qoset.create(symbolMap.values());
        try {
            for (Map.Entry<FunctionSymbol, FunctionSymbol> entryF : symbolMap.entrySet()) {
                FunctionSymbol f = entryF.getKey();
                FunctionSymbol filteredF = entryF.getValue();
                if (knownTrue.contains(this.factFactory.getVarBot(f))) {
                    qoset.setMinimal(filteredF);
                }
                for (Map.Entry<FunctionSymbol, FunctionSymbol> entryG : symbolMap.entrySet()) {
                    FunctionSymbol g = entryG.getKey();
                    if (knownTrue.contains(this.factFactory.getVarSucc(f,g))) {
                        FunctionSymbol filteredG = entryG.getValue();
                        qoset.setGreater(filteredF, filteredG);
                    }
                    if (knownTrue.contains(this.factFactory.getVarEqual(f,g))) {
                        FunctionSymbol filteredG = entryG.getValue();
                        qoset.setEquivalent(filteredF, filteredG);
                    }
                }
            }
        } catch (OrderedSetException e) {
            e.printStackTrace();
            assert false : e.getMessage();
        }
        return new AfsOrder(afs, QLPO.create(qoset));
    }

    @Override
    protected Formula<None> encodeGENGRNonCollapsing(TRSTerm s, TRSFunctionApplication sApp, TRSTerm t, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        FunctionSymbol f = sApp.getRootSymbol();
        FunctionSymbol g = tApp.getRootSymbol();
        if (f.equals(g)) {
            return this.encodeConjunction(sApp, tApp, OrderRelation.GENGR, knownValues);
        }
        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        // f and g could be equal according to the precedence if g is not collapsing
        Variable<None> varEqualFG = this.factFactory.getVarEqual(f,g);
        Formula<None> eVarEqualFG = varEqualFG.evaluate(knownValues);
        Variable<None> varFlagG = this.factFactory.getVarFlag(g);
        Formula<None> eVarFlagG = varFlagG.evaluate(knownValues);
        if (eVarEqualFG != this.ZERO && eVarFlagG != this.ZERO) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(varEqualFG);
            newValues.update(varFlagG);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarEqualFG);
            cArgs.add(eVarFlagG);
            cArgs.add(this.encodeQLPOEqual(sApp, tApp, newValues));
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
        }
        // collapsing g
        NotFormula<None> notFlagG = this.factFactory.getNotFlag(g);
        Formula<None> eNotFlagG = notFlagG.evaluate(knownValues);
        if (eNotFlagG != this.ZERO) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(notFlagG);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eNotFlagG);
            cArgs.add(this.encodeConjunction(s, tApp, OrderRelation.GENGR, newValues));
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
        }
        return this.formulaFactory.buildOr(dArgs);
    }

    protected Formula<None> encodeQLPOEqual(TRSFunctionApplication sApp, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        if (sApp.getRootSymbol().getArity() < QLPOEncoder.BLOWUP_THRESHOLD && tApp.getRootSymbol().getArity() < QLPOEncoder.BLOWUP_THRESHOLD) {
            return this.encodeQLPOEqualSmall(0, sApp, 0, tApp, knownValues);
        }
        return this.encodeQLPOEqual(0, sApp, 0, tApp, knownValues);
    }

    protected Formula<None> encodeQLPOEqualSmall(int i, TRSFunctionApplication sApp, int j, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        if (aprove.Globals.DEBUG_NOWONDER) {
            System.err.println(sApp+"/"+i+" =QLPO "+tApp+"/"+j);
        }
        FunctionSymbol f = sApp.getRootSymbol();
        FunctionSymbol g = tApp.getRootSymbol();
        int fArity = f.getArity();
        int gArity = g.getArity();
        if (!(i < fArity)) {
            if (!(j < gArity)) {
                if (aprove.Globals.DEBUG_NOWONDER) {
                    System.err.println("NO MORE ARGS");
                }
                return this.ONE;
            }
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            for (int k = j; k < gArity; k++) {
                // TODO evaluate destroys DAG, should be fixed for efficiency!!!
                cArgs.add(this.factFactory.getNotArg(g, k).evaluate(knownValues));
            }
            if (aprove.Globals.DEBUG_NOWONDER) {
                System.err.println("ONLY RIGHT ARGS");
            }
            return this.formulaFactory.buildAnd(cArgs);
        }
        if (!(j < gArity)) {
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            for (int k = i; k < fArity; k++) {
                cArgs.add(this.factFactory.getNotArg(f, k).evaluate(knownValues));
            }
            if (aprove.Globals.DEBUG_NOWONDER) {
                System.err.println("ONLY LEFT ARGS");
            }
            return this.formulaFactory.buildAnd(cArgs);
        }
        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        NotFormula<None> notFArgI = this.factFactory.getNotArg(f, i);
        Formula<None> eNotFArgI = notFArgI.evaluate(knownValues);
        if (eNotFArgI != this.ZERO) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(notFArgI);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eNotFArgI);
            cArgs.add(this.encodeQLPOEqualSmall(i+1, sApp, j, tApp, newValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return formula;
            }
            dArgs.add(formula);
        }
        Variable<None> varFArgI = this.factFactory.getVarArg(f, i);
        Formula<None> eVarFArgI = varFArgI.evaluate(knownValues);
        NotFormula<None> notGArgJ = this.factFactory.getNotArg(g, j);
        Formula<None> eNotGArgJ = notGArgJ.evaluate(knownValues);
        if (eVarFArgI != this.ZERO && eNotGArgJ != this.ZERO) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(varFArgI);
            newValues.update(notGArgJ);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarFArgI);
            cArgs.add(eNotGArgJ);
            cArgs.add(this.encodeQLPOEqualSmall(i, sApp, j+1, tApp, newValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return formula;
            }
            dArgs.add(formula);
        }
        Variable<None> varGArgJ = this.factFactory.getVarArg(g, j);
        Formula<None> eVarGArgJ = varGArgJ.evaluate(knownValues);
        if (eVarFArgI != this.ZERO && eVarGArgJ != this.ZERO) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(varFArgI);
            newValues.update(varGArgJ);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarFArgI);
            cArgs.add(eVarGArgJ);
            cArgs.add(this.encodeGENGR(sApp.getArgument(i), tApp.getArgument(j), newValues));
            cArgs.add(this.encodeQLPOEqualSmall(i+1, sApp, j+1, tApp, newValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return formula;
            }
            dArgs.add(formula);
        }
        return this.formulaFactory.buildOr(dArgs);
    }

    protected Formula<None> encodeQLPOEqual(int i, TRSFunctionApplication sApp, int j, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        if (aprove.Globals.DEBUG_NOWONDER) {
            System.err.println(sApp+"/"+i+" =QLPO "+tApp+"/"+j);
        }
        Triple<Pair<Integer, TRSFunctionApplication>, Pair<Integer, TRSFunctionApplication>, ValueCache<None>> id = new Triple<Pair<Integer, TRSFunctionApplication>, Pair<Integer, TRSFunctionApplication>, ValueCache<None>>(new Pair<Integer, TRSFunctionApplication>(i, sApp), new Pair<Integer, TRSFunctionApplication>(j, tApp), knownValues);
        Formula<None> knownResult = this.knownQLPOEqual.get(id);
        if (knownResult != null) {
            if (aprove.Globals.DEBUG_NOWONDER) {
                System.err.println("REUSED CACHE");
            }
            return knownResult;
        }
        FunctionSymbol f = sApp.getRootSymbol();
        FunctionSymbol g = tApp.getRootSymbol();
        int fArity = f.getArity();
        int gArity = g.getArity();
        if (!(i < fArity)) {
            if (!(j < gArity)) {
                if (aprove.Globals.DEBUG_NOWONDER) {
                    System.err.println("NO MORE ARGS");
                }
                return this.updateQLPOEqual(id, this.ONE);
            }
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            for (int k = j; k < gArity; k++) {
                // TODO evaluate destroys DAG, should be fixed for efficiency!!!
                cArgs.add(this.factFactory.getNotArg(g, k).evaluate(knownValues));
            }
            if (aprove.Globals.DEBUG_NOWONDER) {
                System.err.println("ONLY RIGHT ARGS");
            }
            return this.updateQLPOEqual(id, this.formulaFactory.buildAnd(cArgs));
        }
        if (!(j < gArity)) {
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            for (int k = i; k < fArity; k++) {
                cArgs.add(this.factFactory.getNotArg(f, k).evaluate(knownValues));
            }
            if (aprove.Globals.DEBUG_NOWONDER) {
                System.err.println("ONLY LEFT ARGS");
            }
            return this.updateQLPOEqual(id, this.formulaFactory.buildAnd(cArgs));
        }
        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        NotFormula<None> notFArgI = this.factFactory.getNotArg(f, i);
        Formula<None> eNotFArgI = notFArgI.evaluate(knownValues);
        if (eNotFArgI != this.ZERO) {
            //ValueCache newValues = knownValues.copy();
            //newValues.update(notFArgI);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eNotFArgI);
            cArgs.add(this.encodeQLPOEqual(i+1, sApp, j, tApp, knownValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return this.updateQLPOEqual(id, formula);
            }
            dArgs.add(formula);
        }
        Variable<None> varFArgI = this.factFactory.getVarArg(f, i);
        Formula<None> eVarFArgI = varFArgI.evaluate(knownValues);
        NotFormula<None> notGArgJ = this.factFactory.getNotArg(g, j);
        Formula<None> eNotGArgJ = notGArgJ.evaluate(knownValues);
        if (eVarFArgI != this.ZERO && eNotGArgJ != this.ZERO) {
            //ValueCache newValues = knownValues.copy();
            //newValues.update(varFArgI);
            //newValues.update(notGArgJ);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarFArgI);
            cArgs.add(eNotGArgJ);
            cArgs.add(this.encodeQLPOEqual(i, sApp, j+1, tApp, knownValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return this.updateQLPOEqual(id, formula);
            }
            dArgs.add(formula);
        }
        Variable<None> varGArgJ = this.factFactory.getVarArg(g, j);
        Formula<None> eVarGArgJ = varGArgJ.evaluate(knownValues);
        if (eVarFArgI != this.ZERO && eVarGArgJ != this.ZERO) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(varFArgI);
            newValues.update(varGArgJ);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarFArgI);
            cArgs.add(eVarGArgJ);
            cArgs.add(this.encodeGENGR(sApp.getArgument(i), tApp.getArgument(j), newValues));
            cArgs.add(this.encodeQLPOEqual(i+1, sApp, j+1, tApp, knownValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return this.updateQLPOEqual(id, formula);
            }
            dArgs.add(formula);
        }
        return this.updateQLPOEqual(id, this.formulaFactory.buildOr(dArgs));
    }

    private Formula<None> updateQLPOEqual(Triple<Pair<Integer, TRSFunctionApplication>, Pair<Integer, TRSFunctionApplication>, ValueCache<None>> id, Formula<None> formula) {
        if (aprove.Globals.DEBUG_NOWONDER) {
            System.err.println("Storing in Equal cache: "+id);
        }
        this.knownQLPOEqual.put(id, formula);
        return formula;
    }

}
