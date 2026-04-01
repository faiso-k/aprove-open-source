package aprove.verification.dpframework.Orders.SAT;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

public class LPOEncoder extends AbstractLPOEncoder {

    public LPOEncoder(FormulaFactory<None> formulaFactory) {
        this(formulaFactory, 0);
    }

    public LPOEncoder(FormulaFactory<None> formulaFactory, int restriction) {
        super(formulaFactory, restriction);
        this.tryStatus = false;
        this.allowQuasi = false;
    }

    /**
     * <pre>
% encoding of S=[F|SArgs]>[G|TArgs]=T when F & G are noncollapsing
%                                  %%% Constraint=(C1+C2*C3))
%                                  %%% C2=(F>G) or F=G*lex
%
%
gt_lpo_non_collapsing(S,[F|SArgs],T,[G|TArgs],True,Constraint) :-
    disjunction(ge,term(F,1,SArgs),term(T),True,C1),
    (C1==1 -> Tmp=1 ;
        (F\=G -> evaluate(F>G,True,C2) ;
            lex_lpo(F,1,SArgs,TArgs,True,C2)
        ),
        (C2==0 -> C3=0;
            update(C2,True,NewTrue),
            conjunction(gt,term(S),term(G,1,TArgs),NewTrue,C3)
        ),
        simplify(C2*C3,Tmp)
    ),
    simplify(C1+Tmp,Constraint).
     * </pre>
     * @param s
     * @param sApp
     * @param t
     * @param tApp
     * @param knownValues
     * @return
     */
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
            formula = this.factFactory.getVarSucc(f,g).evaluate(knownValues);
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

    protected Formula<None> encodeArgCompare(TRSFunctionApplication sApp, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        return this.encodeLPOLex(0, sApp, tApp, knownValues);
    }

    /**
     * <pre>
% lex_lpo(F,I,[S|Ss],[T|Ts],True,Constraint) :-
%         Constraint = F/I*S>T + not(F/I)*Ss>Ts + S=T*Ss>Ts
%                    = F/I*S>T + (not(F/I) + S=T)*Ss>Ts
lex_lpo(_,_,[],[],_,0).
lex_lpo(F,I,[S|Ss],[T|Ts],True,Constraint) :- I1 is I+1,
    evaluate(F/I,True,FI),
    mysort([F/I|True],NewTrue),
    (FI==0 -> C1=0 ; gt_lpo(S,T,NewTrue,C1)),
    simplify(FI*C1,T1),
    (T1==1 -> T3=1 ;
        evaluate(not(F/I),True,NotFI),
        (NotFI==1 -> C3=1 ; gequals(S,T,NewTrue,C3)),
        simplify(NotFI+C3,T2),
        (T2==0 -> C2=0 ;
            update(T2,True,NewTrue2),
            lex_lpo(F,I1,Ss,Ts,NewTrue2,C2)
        ),
        simplify(T2*C2,T3)
    ),
    simplify(T1+T3,Constraint).
     * </pre>
     * @param i
     * @param sApp
     * @param tApp
     * @param knownValues
     * @return
     */
    protected Formula<None> encodeLPOLex(int i, TRSFunctionApplication sApp, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        FunctionSymbol f = sApp.getRootSymbol();
        if (Globals.useAssertions) {
            assert f.equals(tApp.getRootSymbol());
        }
        if (!(i < f.getArity())) {
            return this.ZERO;
        }
        List<? extends TRSTerm> si = sApp.getArguments();
        List<? extends TRSTerm> ti = tApp.getArguments();
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        Variable<None> varFArgI = this.factFactory.getVarArg(f, i);
        Formula<None> eVarFArgI = varFArgI.evaluate(knownValues);
        ValueCache<None> newValues = knownValues.copy();
        newValues.update(varFArgI);
        if (eVarFArgI != this.ZERO) {
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarFArgI);
            cArgs.add(this.encodeGR(si.get(i), ti.get(i), newValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return this.ONE;
            }
            args.add(formula);
        }
        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
        NotFormula<None> notFArgI = this.factFactory.getNotArg(f, i);
        Formula<None> eNotFArgI = notFArgI.evaluate(knownValues);
        Formula<None> formula = this.ONE;
        if (eNotFArgI != this.ONE) {
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            dArgs.add(eNotFArgI);
            dArgs.add(this.encodeGENGR(si.get(i), ti.get(i), knownValues));
            formula = this.formulaFactory.buildOr(dArgs);
        }
        cArgs.add(formula);
        if (formula != this.ZERO) {
            ValueCache<None> newerValues = knownValues.copy();
            newerValues.update(formula);
            cArgs.add(this.encodeLPOLex(i+1, sApp, tApp, newerValues));
        }
        args.add(this.formulaFactory.buildAnd(cArgs));
        return this.formulaFactory.buildOr(args);
    }

    @Override
    public AfsOrder getOrder(Set<Variable<None>> knownTrue, Afs afs) {
        Map<FunctionSymbol, FunctionSymbol> symbolMap = afs.getSymbolMap(this.sig);
        Poset<FunctionSymbol> poset = Poset.create(symbolMap.values());
        try {
            for (Map.Entry<FunctionSymbol, FunctionSymbol> entryF : symbolMap.entrySet()) {
                FunctionSymbol f = entryF.getKey();
                FunctionSymbol filteredF = entryF.getValue();
                if (knownTrue.contains(this.factFactory.getVarBot(f))) {
                    poset.setMinimal(filteredF);
                }
                for (Map.Entry<FunctionSymbol, FunctionSymbol> entryG : symbolMap.entrySet()) {
                    FunctionSymbol g = entryG.getKey();
                    if (knownTrue.contains(this.factFactory.getVarSucc(f,g))) {
                        FunctionSymbol filteredG = entryG.getValue();
                        poset.setGreater(filteredF, filteredG);
                    }
                }
            }
        } catch (OrderedSetException e) {
            e.printStackTrace();
            assert false : e.getMessage();
        }
        return new AfsOrder(afs, LPO.create(poset));
    }

    @Override
    protected Formula<None> encodeGENGRNonCollapsing(TRSTerm s, TRSFunctionApplication sApp, TRSTerm t, TRSFunctionApplication tApp, ValueCache<None> knownValues) {
        FunctionSymbol f = sApp.getRootSymbol();
        FunctionSymbol g = tApp.getRootSymbol();
        if (f.equals(g)) {
            return this.encodeConjunction(sApp, tApp, OrderRelation.GENGR, knownValues);
        }
        // collapsing g
        NotFormula<None> notFlagG = this.factFactory.getNotFlag(g);
        Formula<None> eNotFlagG = notFlagG.evaluate(knownValues);
        if (eNotFlagG == this.ZERO) {
            return eNotFlagG;
        }
        knownValues.update(notFlagG);
        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
        cArgs.add(eNotFlagG);
        cArgs.add(this.encodeConjunction(s, tApp, OrderRelation.GENGR, knownValues));
        return this.formulaFactory.buildAnd(cArgs);
    }

}
