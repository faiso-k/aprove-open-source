package aprove.verification.dpframework.Orders.SAT;

import java.util.*;
import java.util.Map.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class FactFactory {

    private Map<FunctionSymbol, Variable<None>> f2varFlag = new HashMap<FunctionSymbol, Variable<None>>();
    private Map<FunctionSymbol, Variable<None>[]> f2varArgs = new HashMap<FunctionSymbol, Variable<None>[]>();
    private Map<FunctionSymbol, Variable<None>> f2varDir = new HashMap<FunctionSymbol, Variable<None>>();
    private Map<FunctionSymbol, NotFormula<None>> f2notFlag = new HashMap<FunctionSymbol, NotFormula<None>>();
    private Map<FunctionSymbol, NotFormula<None>[]> f2notArgs = new HashMap<FunctionSymbol, NotFormula<None>[]>();
    private Map<FunctionSymbol, NotFormula<None>> f2notDir = new HashMap<FunctionSymbol, NotFormula<None>>();
    private Map<FunctionSymbol, Variable<None>> f2varBot = new HashMap<FunctionSymbol, Variable<None>>();
    private Map<Pair<FunctionSymbol, FunctionSymbol>, Variable<None>> f2varSucc = new HashMap<Pair<FunctionSymbol, FunctionSymbol>, Variable<None>>();
    private Map<Pair<FunctionSymbol, FunctionSymbol>, Variable<None>> f2varEqual = new HashMap<Pair<FunctionSymbol, FunctionSymbol>, Variable<None>>();
    private Map<Pair<FunctionSymbol, FunctionSymbol>, NotFormula<None>> f2notSucc = new HashMap<Pair<FunctionSymbol, FunctionSymbol>, NotFormula<None>>();
    private Map<Pair<FunctionSymbol, FunctionSymbol>, NotFormula<None>> f2notEqual = new HashMap<Pair<FunctionSymbol, FunctionSymbol>, NotFormula<None>>();
    private Map<Pair<TRSFunctionApplication, TRSFunctionApplication>, Variable<None>[][]> t2varMultiSuccGr = new HashMap<Pair<TRSFunctionApplication, TRSFunctionApplication>, Variable<None>[][]>();
    private Map<Pair<TRSFunctionApplication, TRSFunctionApplication>, NotFormula<None>[][]> t2notMultiSuccGr = new HashMap<Pair<TRSFunctionApplication, TRSFunctionApplication>, NotFormula<None>[][]>();
    private Map<Pair<TRSFunctionApplication, TRSFunctionApplication>, Variable<None>[][]> t2varMultiSuccEq = new HashMap<Pair<TRSFunctionApplication, TRSFunctionApplication>, Variable<None>[][]>();
    private Map<Pair<TRSFunctionApplication, TRSFunctionApplication>, NotFormula<None>[][]> t2notMultiSuccEq = new HashMap<Pair<TRSFunctionApplication, TRSFunctionApplication>, NotFormula<None>[][]>();
    private Map<Pair<TRSFunctionApplication, TRSFunctionApplication>, Variable<None>[][]> t2varMultiSimEq = new HashMap<Pair<TRSFunctionApplication, TRSFunctionApplication>, Variable<None>[][]>();
    private Map<Pair<TRSFunctionApplication, TRSFunctionApplication>, NotFormula<None>[][]> t2notMultiSimEq = new HashMap<Pair<TRSFunctionApplication, TRSFunctionApplication>, NotFormula<None>[][]>();
    private Map<FunctionSymbol, Variable<None>> f2varStatus = new HashMap<FunctionSymbol, Variable<None>>();
    private Map<FunctionSymbol, NotFormula<None>> f2notStatus = new HashMap<FunctionSymbol, NotFormula<None>>();
    private Map<FunctionSymbol, Variable<None>[][]> f2varPerm = new HashMap<FunctionSymbol, Variable<None>[][]>();
    private Map<FunctionSymbol, NotFormula<None>[][]> f2notPerm = new HashMap<FunctionSymbol, NotFormula<None>[][]>();
    private Map<FunctionSymbol, Variable<None>[][]> f2varMrep = new HashMap<FunctionSymbol, Variable<None>[][]>();
    private Map<FunctionSymbol, NotFormula<None>[][]> f2notMrep = new HashMap<FunctionSymbol, NotFormula<None>[][]>();
    private FormulaFactory<None> formulaFactory;

    public FactFactory(FormulaFactory<None> formulaFactory) {
        this.formulaFactory = formulaFactory;
    }

    public Variable<None> getVarFlag(FunctionSymbol f) {
        Variable<None> varFlag = this.f2varFlag.get(f);
        if (varFlag == null) {
            varFlag = this.formulaFactory.buildVariable();
            this.f2varFlag.put(f, varFlag);
        }
        return varFlag;
    }
    public NotFormula<None> getNotFlag(FunctionSymbol f) {
        NotFormula<None> notFlag = this.f2notFlag.get(f);
        if (notFlag == null) {
            notFlag = (NotFormula<None>) this.formulaFactory.buildNot(this.getVarFlag(f));
            this.f2notFlag.put(f, notFlag);
        }
        return notFlag;
    }

    public Variable<None> getVarArg(FunctionSymbol f, int i) {
        return this.getVarArgs(f)[i];
    }
    public Variable<None>[] getVarArgs(FunctionSymbol f) {
        Variable<None>[] vars = this.f2varArgs.get(f);
        if (vars == null) {
            int arity = f.getArity();
            vars = new Variable[arity];
            for (int j = 0; j < arity; j++) {
                vars[j] = this.formulaFactory.buildVariable();
            }
            this.f2varArgs.put(f, vars);
        }
        return vars;
    }
    public NotFormula<None> getNotArg(FunctionSymbol f, int i) {
        return this.getNotArgs(f)[i];
    }
    public NotFormula<None>[] getNotArgs(FunctionSymbol f) {
        NotFormula<None>[] nots = this.f2notArgs.get(f);
        if (nots == null) {
            int arity = f.getArity();
            nots = new NotFormula[arity];
            Variable<None>[] vars = this.getVarArgs(f);
            for (int j = 0; j < arity; j++) {
                nots[j] = (NotFormula<None>) this.formulaFactory.buildNot(vars[j]);
            }
            this.f2notArgs.put(f, nots);
        }
        return nots;
    }

    public Variable<None> getVarBot(FunctionSymbol f) {
        Variable<None> varBot = this.f2varBot.get(f);
        if (varBot == null) {
            varBot = this.formulaFactory.buildVariable();
            this.f2varBot.put(f, varBot);
        }
        return varBot;
    }

    public Variable<None> getVarSucc(FunctionSymbol f, FunctionSymbol g) {
        Pair<FunctionSymbol, FunctionSymbol> fg = new Pair<FunctionSymbol, FunctionSymbol>(f,g);
        Variable<None> varSucc = this.f2varSucc.get(fg);
        if (varSucc == null) {
            varSucc = this.formulaFactory.buildVariable();
            this.f2varSucc.put(fg, varSucc);
        }
        return varSucc;
    }
    public NotFormula<None> getNotSucc(FunctionSymbol f, FunctionSymbol g) {
        Pair<FunctionSymbol, FunctionSymbol> fg = new Pair<FunctionSymbol, FunctionSymbol>(f,g);
        NotFormula<None> notSucc = this.f2notSucc.get(fg);
        if (notSucc == null) {
            Variable<None> varSucc = this.getVarSucc(f, g);
            notSucc = (NotFormula<None>) this.formulaFactory.buildNot(varSucc);
            this.f2notSucc.put(fg, notSucc);
        }
        return notSucc;
    }

    public Variable<None> getVarEqual(FunctionSymbol f, FunctionSymbol g) {
        Pair<FunctionSymbol, FunctionSymbol> fg = new Pair<FunctionSymbol, FunctionSymbol>(f,g);
        Variable<None> varEqual = this.f2varEqual.get(fg);
        if (varEqual == null) {
            varEqual = this.formulaFactory.buildVariable();
            this.f2varEqual.put(fg, varEqual);
            Pair<FunctionSymbol, FunctionSymbol> gf = new Pair<FunctionSymbol, FunctionSymbol>(g,f);
            this.f2varEqual.put(gf, varEqual);
        }
        return varEqual;
    }
    public NotFormula<None> getNotEqual(FunctionSymbol f, FunctionSymbol g) {
        Pair<FunctionSymbol, FunctionSymbol> fg = new Pair<FunctionSymbol, FunctionSymbol>(f,g);
        NotFormula<None> notEqual = this.f2notEqual.get(fg);
        if (notEqual == null) {
            Variable<None> varEqual = this.getVarEqual(f, g);
            notEqual = (NotFormula<None>) this.formulaFactory.buildNot(varEqual);
            this.f2notSucc.put(fg, notEqual);
        }
        return notEqual;
    }

    public Map<Variable<None>, Fact> getFactMap() {
        Map<Variable<None>, Fact> factMap = new HashMap<Variable<None>, Fact>();
        for (Entry<FunctionSymbol, Variable<None>> entry : this.f2varFlag.entrySet()) {
            factMap.put(entry.getValue(), new FactFlag(entry.getKey()));
        }
        for (Entry<FunctionSymbol, Variable<None>[]> entry : this.f2varArgs.entrySet()) {
            FunctionSymbol f = entry.getKey();
            Variable<None>[] vars = entry.getValue();
            for (int i = 0; i < vars.length; i++) {
                factMap.put(vars[i], new FactArg(f, i));
            }
        }
        for (Entry<FunctionSymbol, Variable<None>> entry : this.f2varBot.entrySet()) {
            factMap.put(entry.getValue(), new FactBot(entry.getKey()));
        }
        for (Entry<Pair<FunctionSymbol, FunctionSymbol>, Variable<None>> entry : this.f2varSucc.entrySet()) {
            Pair<FunctionSymbol, FunctionSymbol> fg = entry.getKey();
            factMap.put(entry.getValue(), new FactSucc(fg.x, fg.y));
        }
        for (Entry<Pair<FunctionSymbol, FunctionSymbol>, Variable<None>> entry : this.f2varEqual.entrySet()) {
            Pair<FunctionSymbol, FunctionSymbol> fg = entry.getKey();
            int res = fg.x.compareTo(fg.y);
            if (Globals.useAssertions) {
                assert res != 0;
            }
            if (res < 0) {
                factMap.put(entry.getValue(), new FactEqual(fg.x, fg.y));
            }
        }
        for (Entry<FunctionSymbol, Variable<None>> entry : this.f2varDir.entrySet()) {
            factMap.put(entry.getValue(), new FactDir(entry.getKey()));
        }
        for (Entry<Pair<TRSFunctionApplication, TRSFunctionApplication>, Variable<None>[][]> entry : this.t2varMultiSuccEq.entrySet()) {
            Pair<TRSFunctionApplication, TRSFunctionApplication> st = entry.getKey();
            Variable<None>[][] vars = entry.getValue();
            for (int i = 0; i < vars.length; i++) {
                for (int j = 0; j < vars[i].length; j++) {
                    factMap.put(vars[i][j], new FactMultiSuccEq(st.x, st.y, i, j));
                }
            }
        }
        for (Entry<Pair<TRSFunctionApplication, TRSFunctionApplication>, Variable<None>[][]> entry : this.t2varMultiSuccGr.entrySet()) {
            Pair<TRSFunctionApplication, TRSFunctionApplication> st = entry.getKey();
            Variable<None>[][] vars = entry.getValue();
            for (int i = 0; i < vars.length; i++) {
                for (int j = 0; j < vars[i].length; j++) {
                    factMap.put(vars[i][j], new FactMultiSuccGr(st.x, st.y, i, j));
                }
            }
        }
        for (Entry<Pair<TRSFunctionApplication, TRSFunctionApplication>, Variable<None>[][]> entry : this.t2varMultiSimEq.entrySet()) {
            Pair<TRSFunctionApplication, TRSFunctionApplication> st = entry.getKey();
            Variable<None>[][] vars = entry.getValue();
            for (int i = 0; i < vars.length; i++) {
                for (int j = 0; j < vars[i].length; j++) {
                    factMap.put(vars[i][j], new FactMultiSimEq(st.x, st.y, i, j));
                }
            }
        }
        for (Entry<FunctionSymbol, Variable<None>> entry : this.f2varStatus.entrySet()) {
            factMap.put(entry.getValue(), new FactStatus(entry.getKey()));
        }
        for (Entry<FunctionSymbol, Variable<None>[][]> entry : this.f2varPerm.entrySet()) {
            FunctionSymbol f = entry.getKey();
            Variable<None>[][] vars = entry.getValue();
            for (int i = 0; i < vars.length; i++) {
                for (int j = 0; j < vars[i].length; j++) {
                    factMap.put(vars[i][j], new FactPerm(f, i, j));
                }
            }
        }
        for (Entry<FunctionSymbol, Variable<None>[][]> entry : this.f2varMrep.entrySet()) {
            FunctionSymbol f = entry.getKey();
            Variable<None>[][] vars = entry.getValue();
            for (int i = 0; i < vars.length; i++) {
                for (int l = 0; l < vars[i].length; l++) {
                    factMap.put(vars[i][l], new FactMrep(f, i, l));
                }
            }
        }
        return factMap;
    }

    public Variable<None> getVarDir(FunctionSymbol f) {
        Variable<None> varDir = this.f2varDir.get(f);
        if (varDir == null) {
            varDir = this.formulaFactory.buildVariable();
            this.f2varDir.put(f, varDir);
        }
        return varDir;
    }
    public NotFormula<None> getNotDir(FunctionSymbol f) {
        NotFormula<None> notDir = this.f2notDir.get(f);
        if (notDir == null) {
            notDir = (NotFormula<None>) this.formulaFactory.buildNot(this.getVarDir(f));
            this.f2notDir.put(f, notDir);
        }
        return notDir;
    }

    /* Probably not needed. Untested.
    public Set<FunctionSymbol> getAfsSignature() {
        Set<FunctionSymbol> sig = new LinkedHashSet<FunctionSymbol>();
        sig.addAll(f2varFlag.keySet());
        sig.addAll(f2varArgs.keySet());
        return sig;
    }

    public Set<FunctionSymbol> getPOSignature() {
        Set<FunctionSymbol> sig = new LinkedHashSet<FunctionSymbol>();
        sig.addAll(f2varBot.keySet());
        for (Pair<FunctionSymbol, FunctionSymbol> pair : f2varSucc.keySet()) {
            sig.add(pair.x);
            sig.add(pair.y);
        }
        for (Pair<FunctionSymbol, FunctionSymbol> pair : f2varEqual.keySet()) {
            sig.add(pair.x);
            sig.add(pair.y);
        }
        return sig;
    }*/

    public Map<Pair<TRSFunctionApplication, TRSFunctionApplication>, Variable<None>[][]> getVarMultiSuccGr() {
        return this.t2varMultiSuccGr;
    }
    public Variable<None> getVarMultiSuccGr(TRSFunctionApplication s, TRSFunctionApplication t, int i, int j) {
        return this.getVarMultiSuccGr(s, t)[i][j];
    }
    public Variable<None>[][] getVarMultiSuccGr(TRSFunctionApplication s, TRSFunctionApplication t) {
        Pair<TRSFunctionApplication, TRSFunctionApplication> st = new Pair<TRSFunctionApplication, TRSFunctionApplication>(s,t);
        Variable<None>[][] vars = this.t2varMultiSuccGr.get(st);
        if (vars == null) {
            int fArity = s.getRootSymbol().getArity();
            int gArity = t.getRootSymbol().getArity();
            vars = new Variable[fArity][gArity];
            for (int i = 0; i < fArity; i++) {
                for (int j = 0; j < gArity; j++) {
                    vars[i][j] = this.formulaFactory.buildVariable();
                }
            }
            this.t2varMultiSuccGr.put(st, vars);
        }
        return vars;
    }
    public NotFormula<None> getNotMultiSuccGr(TRSFunctionApplication s, TRSFunctionApplication t, int i, int j) {
        return this.getNotMultiSuccGr(s, t)[i][j];
    }
    public NotFormula<None>[][] getNotMultiSuccGr(TRSFunctionApplication s, TRSFunctionApplication t) {
        Pair<TRSFunctionApplication, TRSFunctionApplication> st = new Pair<TRSFunctionApplication, TRSFunctionApplication>(s,t);
        NotFormula<None>[][] nots = this.t2notMultiSuccGr.get(st);
        if (nots == null) {
            int fArity = s.getRootSymbol().getArity();
            int gArity = t.getRootSymbol().getArity();
            Variable<None>[][] vars = this.getVarMultiSuccGr(s, t);
            nots = new NotFormula[fArity][gArity];
            for (int i = 0; i < fArity; i++) {
                for (int j = 0; j < gArity; j++) {
                    nots[i][j] = (NotFormula<None>) this.formulaFactory.buildNot(vars[i][j]);
                }
            }
            this.t2notMultiSuccGr.put(st, nots);
        }
        return nots;
    }

    public Map<Pair<TRSFunctionApplication, TRSFunctionApplication>, Variable<None>[][]> getVarMultiSuccEq() {
        return this.t2varMultiSuccEq;
    }
    public Variable<None> getVarMultiSuccEq(TRSFunctionApplication s, TRSFunctionApplication t, int i, int j) {
        return this.getVarMultiSuccEq(s, t)[i][j];
    }
    public Variable<None>[][] getVarMultiSuccEq(TRSFunctionApplication s, TRSFunctionApplication t) {
        Pair<TRSFunctionApplication, TRSFunctionApplication> st = new Pair<TRSFunctionApplication, TRSFunctionApplication>(s,t);
        Variable<None>[][] vars = this.t2varMultiSuccEq.get(st);
        if (vars == null) {
            int fArity = s.getRootSymbol().getArity();
            int gArity = t.getRootSymbol().getArity();
            vars = new Variable[fArity][gArity];
            for (int i = 0; i < fArity; i++) {
                for (int j = 0; j < gArity; j++) {
                    vars[i][j] = this.formulaFactory.buildVariable();
                }
            }
            this.t2varMultiSuccEq.put(st, vars);
        }
        return vars;
    }
    public NotFormula<None> getNotMultiSuccEq(TRSFunctionApplication s, TRSFunctionApplication t, int i, int j) {
        return this.getNotMultiSuccEq(s, t)[i][j];
    }
    public NotFormula<None>[][] getNotMultiSuccEq(TRSFunctionApplication s, TRSFunctionApplication t) {
        Pair<TRSFunctionApplication, TRSFunctionApplication> st = new Pair<TRSFunctionApplication, TRSFunctionApplication>(s,t);
        NotFormula<None>[][] nots = this.t2notMultiSuccEq.get(st);
        if (nots == null) {
            int fArity = s.getRootSymbol().getArity();
            int gArity = t.getRootSymbol().getArity();
            Variable<None>[][] vars = this.getVarMultiSuccEq(s, t);
            nots = new NotFormula[fArity][gArity];
            for (int i = 0; i < fArity; i++) {
                for (int j = 0; j < gArity; j++) {
                    nots[i][j] = (NotFormula<None>) this.formulaFactory.buildNot(vars[i][j]);
                }
            }
            this.t2notMultiSuccEq.put(st, nots);
        }
        return nots;
    }

    public Map<Pair<TRSFunctionApplication, TRSFunctionApplication>, Variable<None>[][]> getVarMultiSimEq() {
        return this.t2varMultiSimEq;
    }
    public Variable<None> getVarMultiSimEq(TRSFunctionApplication s, TRSFunctionApplication t, int i, int j) {
        return this.getVarMultiSimEq(s, t)[i][j];
    }
    public Variable<None>[][] getVarMultiSimEq(TRSFunctionApplication s, TRSFunctionApplication t) {
        Pair<TRSFunctionApplication, TRSFunctionApplication> st = new Pair<TRSFunctionApplication, TRSFunctionApplication>(s,t);
        Variable<None>[][] vars = this.t2varMultiSimEq.get(st);
        if (vars == null) {
            int fArity = s.getRootSymbol().getArity();
            int gArity = t.getRootSymbol().getArity();
            vars = new Variable[fArity][gArity];

            for (int i = 0; i < fArity; i++) {
                for (int j = 0; j < gArity; j++) {
                    vars[i][j] = this.formulaFactory.buildVariable();
                }
            }
            this.t2varMultiSimEq.put(st, vars);
        }
        return vars;
    }
    public NotFormula<None> getNotMultiSimEq(TRSFunctionApplication s, TRSFunctionApplication t, int i, int j) {
        return this.getNotMultiSimEq(s, t)[i][j];
    }
    public NotFormula<None>[][] getNotMultiSimEq(TRSFunctionApplication s, TRSFunctionApplication t) {
        Pair<TRSFunctionApplication, TRSFunctionApplication> st = new Pair<TRSFunctionApplication, TRSFunctionApplication>(s,t);
        NotFormula<None>[][] nots = this.t2notMultiSimEq.get(st);
        if (nots == null) {
            int fArity = s.getRootSymbol().getArity();
            int gArity = t.getRootSymbol().getArity();
            Variable<None>[][] vars = this.getVarMultiSimEq(s, t);
            nots = new NotFormula[fArity][gArity];
            for (int i = 0; i < fArity; i++) {
                for (int j = 0; j < gArity; j++) {
                    nots[i][j] = (NotFormula<None>) this.formulaFactory.buildNot(vars[i][j]);
                }
            }
            this.t2notMultiSimEq.put(st, nots);
        }
        return nots;
    }

    public Variable<None> getVarStatus(FunctionSymbol f) {
        Variable<None> varStatus = this.f2varStatus.get(f);
        if (varStatus == null) {
            varStatus = this.formulaFactory.buildVariable();
            this.f2varStatus.put(f, varStatus);
        }
        return varStatus;
    }
    public NotFormula<None> getNotStatus(FunctionSymbol f) {
        NotFormula<None> notStatus = this.f2notStatus.get(f);
        if (notStatus == null) {
            notStatus = (NotFormula<None>) this.formulaFactory.buildNot(this.getVarStatus(f));
            this.f2notStatus.put(f, notStatus);
        }
        return notStatus;
    }

    public Map<FunctionSymbol, Variable<None>[][]> getVarPerm() {
        return this.f2varPerm;
    }
    public Variable<None> getVarPerm(FunctionSymbol f, int i, int j) {
        return this.getVarPerm(f)[i][j];
    }
    public Variable<None>[][] getVarPerm(FunctionSymbol f) {
        Variable<None>[][] vars = this.f2varPerm.get(f);
        if (vars == null) {
            int arity = f.getArity();
            vars = new Variable[arity][arity];
            for (int i = 0; i < arity; i++) {
                for (int j = 0; j < arity; j++) {
                    vars[i][j] = this.formulaFactory.buildVariable();
                }
            }
            this.f2varPerm.put(f, vars);
        }
        return vars;
    }
    public NotFormula<None> getNotPerm(FunctionSymbol f, int i, int j) {
        return this.getNotPerm(f)[i][j];
    }
    public NotFormula<None>[][] getNotPerm(FunctionSymbol f) {
        NotFormula<None>[][] nots = this.f2notPerm.get(f);
        if (nots == null) {
            int arity = f.getArity();
            Variable<None>[][] vars = this.getVarPerm(f);
            nots = new NotFormula[arity][arity];
            for (int i = 0; i < arity; i++) {
                for (int j = 0; j < arity; j++) {
                    nots[i][j] = (NotFormula<None>) this.formulaFactory.buildNot(vars[i][j]);
                }
            }
            this.f2notPerm.put(f, nots);
        }
        return nots;
    }

    public Map<FunctionSymbol, Variable<None>[][]> getVarMrep() {
        return this.f2varMrep;
    }
    public Variable<None>[] getVarMrep(FunctionSymbol f, int i) {
        return this.getVarMrep(f)[i];
    }
    public Variable<None>[][] getVarMrep(FunctionSymbol f) {
        Variable<None>[][] vars = this.f2varMrep.get(f);
        if (vars == null) {
            int arity = f.getArity();
            int logArity;
            if (false) {
                logArity = (int) Math.ceil(Math.log(arity+1)/Math.log(2));
            } else {
                logArity = arity < 1 ? 0 : (int) Math.ceil(Math.log(arity)/Math.log(2));
            }
            vars = new Variable[arity][logArity];
            for (int i = 0; i < arity; i++) {
                for (int j = 0; j < logArity; j++) {
                    vars[i][j] = this.formulaFactory.buildVariable();
                }
            }
            this.f2varMrep.put(f, vars);
        }
        return vars;
    }
    public NotFormula<None>[] getNotMrep(FunctionSymbol f, int i) {
        return this.getNotMrep(f)[i];
    }
    public NotFormula<None>[][] getNotMrep(FunctionSymbol f) {
        NotFormula<None>[][] nots = this.f2notMrep.get(f);
        if (nots == null) {
            int arity = f.getArity();
            int logArity;
            if (false) {
                logArity = (int) Math.ceil(Math.log(arity+1)/Math.log(2));
            } else {
                logArity = arity < 1 ? 0 : (int) Math.ceil(Math.log(arity)/Math.log(2));
            }
            Variable<None>[][] vars = this.getVarMrep(f);
            nots = new NotFormula[arity][logArity];
            for (int i = 0; i < arity; i++) {
                for (int j = 0; j < logArity; j++) {
                    nots[i][j] = (NotFormula<None>) this.formulaFactory.buildNot(vars[i][j]);
                }
            }
            this.f2notMrep.put(f, nots);
        }
        return nots;
    }

}
