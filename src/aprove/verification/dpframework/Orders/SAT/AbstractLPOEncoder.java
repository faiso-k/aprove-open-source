package aprove.verification.dpframework.Orders.SAT;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.PropositionalLogic.ValueCaches.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public abstract class AbstractLPOEncoder implements SATEncoder {

    // formulaFactory must be a factory that does not incorporate the
    // argument list directly into the formula, but makes a copy instead
    protected FormulaFactory<None> formulaFactory;
    protected FactFactory factFactory;
    protected Constant<None> ZERO;
    protected Constant<None> ONE;
    protected SATPatterns<None> patterns;

    /**
     * Relations between terms that have been determined. Boolean.TRUE means
     * that s is greater than t while Boolean.FALSE means that s is greater or
     * equal to t.
     */
    private Map<Triple<TRSTerm, TRSTerm, ValueCache<None>>, Formula<None>> knownGENGR = new HashMap<Triple<TRSTerm, TRSTerm, ValueCache<None>>, Formula<None>>();
    /**
     * Relations between terms that have been determined. Boolean.TRUE means
     * that s is greater than t while Boolean.FALSE means that s is greater or
     * equal to t.
     */
    private Map<Triple<TRSTerm, TRSTerm, ValueCache<None>>, Formula<None>> knownGR = new HashMap<Triple<TRSTerm, TRSTerm, ValueCache<None>>, Formula<None>>();
    /**
     * Signature.
     */
    protected Set<FunctionSymbol> sig;
    /**
     * How many arguments can be regarded at one time? O encodes no limit.
     */
    private int restriction;
    protected boolean tryStatus;
    protected boolean allowQuasi;
    protected boolean noafs = false;

    public AbstractLPOEncoder(FormulaFactory<None> formulaFactory, int restriction) {
        this.formulaFactory = formulaFactory;
        this.ZERO = formulaFactory.buildConstant(false);
        this.ONE = formulaFactory.buildConstant(true);
        this.factFactory = new FactFactory(formulaFactory);
        this.restriction = restriction;
        this.patterns = new SATPatterns<None>(formulaFactory, true);
    }

    public void forceStrongMonotonicity() {
        this.noafs = true;
    }
    /**
     * <pre>
encode(S,N,Constraint) :-
        retractall(lemma_gt_lpo(_,_,_,_)),
        encode_part1(S,N,True,C1),
        (C1==0 -> C2=0 ;
            update(C1,True,True1),
            encode_part2(S,True1,C2)
        ),
        simplify(C1*C2,Constraint),
        prettyprint(Constraint, True1).

% to encode dependency pair problem S,N:
%  part1 *C0 the global parts
%  part1 *C1 for every nonstrict rule in N, s -> t, we have s >= t
%  part1 *C2 for every strict rule s -> t in S, we have s > t or s >= t
%  part2 *C3 for at least one strict rule in S, s -> t, we have s > t

encode_part1(S,N,True,Constraint) :-
        global(S,N,True1,C1),
        forall_ns_lpo(S,True1,C2),
        simplify(C1*C2,T1),
        (T1==0 -> C3=0, True=[] ;
            update(T1,True1,True),
            forall_ns_lpo(N,True,C3)
        ),
        simplify(T1*C3,Constraint).

encode_part2(S,True,Constraint) :-
        exists_s_lpo(S,True,Constraint).
     * </pre>
     * @param strict
     * @param nonStrict
     * @return
     * @throws AbortionException
     */
    @Override
    public POFormula encode(Set<? extends GeneralizedRule> strict, Set<? extends GeneralizedRule> nonStrict, Abortion aborter) throws AbortionException {
        //System.out.println("S = "+strict);
        //System.out.println("N = "+nonStrict);
        // insert simplifies and tests for unsatisfiability

        ValueCache<None> knownValues = new NoValueCache<None>(this.formulaFactory);
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(this.encodeGlobalConstraints(strict, nonStrict, knownValues));
        args.add(this.encodeAllGreaterEqual(strict, knownValues, aborter));
        Formula<None> formula = this.formulaFactory.buildAnd(args);
        if (formula != this.ZERO) {
            args.clear();
            args.add(formula);
            args.add(this.encodeAllGreaterEqual(nonStrict, knownValues, aborter));
            formula = this.formulaFactory.buildAnd(args);
            if (formula != this.ZERO) {
                args.clear();
                args.add(formula);
                args.add(this.encodeOneGreater(strict, knownValues, aborter));
                formula = this.formulaFactory.buildAnd(args);
            }
        }
//        updating is DANGEROUS because it can remove po-constraints
//        TODO maybe add updating AFTER po-encoding
//        knownValues.update(formula);
//        formula = formula.evaluate(knownValues);
        args.clear();
        args.add(formula);
        args.add(this.encodePermutationConstraints(knownValues));
        formula = this.formulaFactory.buildAnd(args);
        POFormula poFormula = new POFormula(formula, this.factFactory.getFactMap(), this.formulaFactory, this.allowQuasi);
        //System.out.println(poFormula);
        return poFormula;
    }

    @Override
    public POFormula encode(Set<? extends GeneralizedRule> strict, Abortion aborter) throws AbortionException {
        ValueCache<None> knownValues = new NoValueCache<None>(this.formulaFactory);
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(this.encodeGlobalConstraints(strict, null, knownValues));
        args.add(this.encodeAllGreater(strict, knownValues, aborter));
        Formula<None> formula = this.formulaFactory.buildAnd(args);
//        updating is DANGEROUS because it can remove po-constraints
//        TODO maybe add updating AFTER po-encoding
//        knownValues.update(formula);
//        formula = formula.evaluate(knownValues);
        args.clear();
        args.add(formula);
        args.add(this.encodePermutationConstraints(knownValues));
        formula = this.formulaFactory.buildAnd(args);
        POFormula poFormula = new POFormula(formula, this.factFactory.getFactMap(), this.formulaFactory, this.allowQuasi);
        //System.out.println(poFormula);
        return poFormula;
    }

    protected Formula<None> encodePermutationConstraints(ValueCache<None> knownValues) {
        return this.ONE;
    }

    @Override
    public POFormula encode(Set<? extends GeneralizedRule> strict, Map<? extends GeneralizedRule, QActiveCondition> activeNonStrict, boolean active, boolean allStrict, Abortion aborter) throws AbortionException {
       ValueCache<None> knownValues = new NoValueCache<None>(this.formulaFactory);
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(this.encodeGlobalConstraints(strict, activeNonStrict.keySet(), knownValues));
        if (allStrict) {
            args.add(this.encodeAllGreater(strict, knownValues, aborter));
        } else {
            args.add(this.encodeAllGreaterEqual(strict, knownValues, aborter));
        }
        Formula<None> formula = this.formulaFactory.buildAnd(args);
        if (formula != this.ZERO) {
            args.clear();
            args.add(formula);
            if (active) {
                args.add(this.encodeAllGreaterEqual(activeNonStrict, knownValues, aborter));
            } else {
                args.add(this.encodeAllGreaterEqual(activeNonStrict.keySet(), knownValues, aborter));
            }
            formula = this.formulaFactory.buildAnd(args);
            if (!allStrict && formula != this.ZERO) {
                args.clear();
                args.add(formula);
                args.add(this.encodeOneGreater(strict, knownValues, aborter));
                formula = this.formulaFactory.buildAnd(args);
            }
        }
        args.clear();
        args.add(formula);
        args.add(this.encodePermutationConstraints(knownValues));
        formula = this.formulaFactory.buildAnd(args);
        POFormula poFormula = new POFormula(formula, this.factFactory.getFactMap(), this.formulaFactory, this.allowQuasi);
        return poFormula;
    }

    /**
     * <pre>
exists_s_lpo([],_,0).
exists_s_lpo([rule(L,R)|Rs],True,Constraint) :-
    gt_lpo(L,R,True,C1),
    (C1==1 -> C2=1 ; exists_s_lpo(Rs,True,C2)),
    simplify(C1+C2,Constraint).
     * </pre>
     * @param rules
     * @return
     * @throws AbortionException
     */
    private Formula<None> encodeOneGreater(Set<? extends GeneralizedRule> rules, ValueCache<None> knownValues, Abortion aborter) throws AbortionException {
        if (rules.size() == 1) {
            GeneralizedRule rule = rules.iterator().next();
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            return this.encodeGR(rule.getLeft(), rule.getRight(), knownValues);
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (GeneralizedRule rule : rules) {
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            aborter.checkAbortion();
            Formula<None> formula = this.encodeGR(rule.getLeft(), rule.getRight(), knownValues);
            if (formula == this.ONE) {
                return formula;
            }
            args.add(formula);
        }
        return this.formulaFactory.buildOr(args);
    }

    /**
     * <pre>
forall_ns_lpo([],_,1).
forall_ns_lpo([rule(L,R)|Rs],True,Constraint) :-
    geq_lpo(L,R,True,C1),
    (C1==0 -> C2=0 ;
        update(C1,True,NewTrue),
        forall_ns_lpo(Rs,NewTrue,C2)
    ),
    simplify(C1*C2,Constraint).
     * </pre>
     * @param rules
     * @param knownValues
     * @return
     * @throws AbortionException
     */
    private Formula<None> encodeAllGreaterEqual(Set<? extends GeneralizedRule> rules, ValueCache<None> knownValues, Abortion aborter) throws AbortionException {
        if (rules.size() == 1) {
            GeneralizedRule rule = rules.iterator().next();
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            Formula<None> formula = this.encodeGE(rule.getLeft(), rule.getRight(), knownValues);
            knownValues.update(formula);
            return formula;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (GeneralizedRule rule : rules) {
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            aborter.checkAbortion();
            Formula<None> formula = this.encodeGE(rule.getLeft(), rule.getRight(), knownValues);
            if (formula == this.ZERO) {
                return formula;
            }
            knownValues.update(formula);
            args.add(formula);
        }
        return this.formulaFactory.buildAnd(args);
    }

    private Formula<None> encodeAllGreater(Set<? extends GeneralizedRule> rules, ValueCache<None> knownValues, Abortion aborter) throws AbortionException {
        if (rules.size() == 1) {
            GeneralizedRule rule = rules.iterator().next();
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            Formula<None> formula = this.encodeGR(rule.getLeft(), rule.getRight(), knownValues);
            knownValues.update(formula);
            return formula;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (GeneralizedRule rule : rules) {
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            aborter.checkAbortion();
            Formula<None> formula = this.encodeGR(rule.getLeft(), rule.getRight(), knownValues);
            if (formula == this.ZERO) {
                return formula;
            }
            knownValues.update(formula);
            args.add(formula);
        }
        return this.formulaFactory.buildAnd(args);
    }

    private Formula<None> encodeAllGreaterEqual(Map<? extends GeneralizedRule, QActiveCondition> activeRules, ValueCache<None> knownValues, Abortion aborter) throws AbortionException {
        if (activeRules.size() == 1) {
            Map.Entry<? extends GeneralizedRule, QActiveCondition> activeRule = activeRules.entrySet().iterator().next();
            GeneralizedRule rule = activeRule.getKey();
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            QActiveCondition activeCond = activeRule.getValue();
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            dArgs.add(this.encodeActiveCondition(activeCond, knownValues));
            dArgs.add(this.encodeGE(rule.getLeft(), rule.getRight(), knownValues));
            Formula<None> formula = this.formulaFactory.buildOr(dArgs);
            knownValues.update(formula);
            return formula;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (Map.Entry<? extends GeneralizedRule, QActiveCondition> activeRule : activeRules.entrySet()) {
            aborter.checkAbortion();
            GeneralizedRule rule = activeRule.getKey();
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+rule);
            }
            QActiveCondition activeCond = activeRule.getValue();
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            dArgs.add(this.encodeActiveCondition(activeCond, knownValues));
            dArgs.add(this.encodeGE(rule.getLeft(), rule.getRight(), knownValues));
            Formula<None> formula = this.formulaFactory.buildOr(dArgs);
            if (formula == this.ZERO) {
                return formula;
            }
            knownValues.update(formula);
            args.add(formula);
        }
        return this.formulaFactory.buildAnd(args);
    }

    private Formula<None> encodeActiveCondition(QActiveCondition activeCond, ValueCache<None> knownValues) {
        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        for (Set<Pair<FunctionSymbol, Integer>> poss : activeCond.getSetRepresentation()) {
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            for (Pair<FunctionSymbol, Integer> pos : poss) {
                cArgs.add(this.factFactory.getVarArg(pos.x, pos.y).evaluate(knownValues));
            }
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
        }
        return this.formulaFactory.buildNot(this.formulaFactory.buildOr(dArgs));
    }

    /**
     * <pre>
geq_lpo(S,T,True,Constraint) :-
    gequals(S,T,True,C1),
    (C1==1 -> C2=1 ; gt_lpo(S,T,True,C2)),
    simplify(C1+C2, Constraint).
     * </pre>
     * @param s
     * @param t
     * @return
     */
    private Formula<None> encodeGE(TRSTerm s, TRSTerm t, ValueCache<None> knownValues) {
        Formula<None> formula = this.encodeGENGR(s,t, knownValues);
        //System.out.println(new POFormula(formula, this.factFactory.getFactMap(), this.varFactory));
        if (formula == this.ONE) {
            return formula;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(formula);
        formula = this.encodeGR(s, t, knownValues);
        //System.out.println(new POFormula(formula, this.factFactory.getFactMap(), this.varFactory));
        args.add(formula);
        return this.formulaFactory.buildOr(args);
    }

    /**
     * <pre>
gequals(S,T,_,Constraint) :- var(S), var(T), !,
    (S==T -> Constraint=1 ; Constraint=0).
gequals(S,T,_, bot(F)) :- var(S),nonvar(T),T=..[F], !.


gequals(S,T,True, Constraint) :- var(S),nonvar(T),T=..[F|TArgs], !,
        evaluate(not(flag(F)),True,NotFlagF),
        (NotFlagF==0 -> C1=0;
            mysort([not(flag(F))|True],NewTrue),
            disjunction(eq,term(S),term(F,1,TArgs),NewTrue,C1)
        ),
        simplify(NotFlagF*C1,Constraint).


gequals(S,T,True,Constraint) :- nonvar(S), S=..[F|SArgs], !,
    %
    % F is noncollapsing
    evaluate(flag(F),True,FlagF),
    (FlagF==0 -> C1=0 ;
        mysort([flag(F)|True],NewTrue1),
        eq_left_noncollapsing(S,[F|SArgs],T,NewTrue1,C1)
    ),
    simplify(FlagF*C1,T1),
    %
    % F is collapsing
    (T1==1 -> T2=1 ;
        evaluate(not(flag(F)),True,NotFlagF),
        (NotFlagF==0 -> C2=0 ;
            mysort([not(flag(F))|True],NewTrue2),
            conjunction(eq,term(F,1,SArgs),term(T),NewTrue2,C2)
        ),
        simplify(NotFlagF*C2,T2)
    ),
    simplify(T1+T2,Constraint).
     * </pre>
     * @param s
     * @param t
     * @return
     */
    protected Formula<None> encodeGENGR(TRSTerm s, TRSTerm t, ValueCache<None> knownValues) {
        Triple<TRSTerm, TRSTerm, ValueCache<None>> stk = new Triple<TRSTerm, TRSTerm, ValueCache<None>>(s, t, knownValues.copy());
        Formula<None> rel = this.knownGENGR.get(stk);
        if (rel != null) {
            return rel;
        }
        Formula<None> vf = this.encodeVarConstraints(s, t, knownValues);
        if (s.isVariable()) {
            if (t.isVariable()) {
                if (s.equals(t)) {
                    return this.updateGENGR(stk, this.ONE, this.ONE);
                }
                return this.updateGENGR(stk, this.ZERO, this.ZERO);
            }
            // case s >= g(t_1, ..., t_n)=t
            TRSFunctionApplication tApp = (TRSFunctionApplication) t;
            FunctionSymbol g = tApp.getRootSymbol();
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            for (int i = 0; i < g.getArity(); i++) {
                cArgs.add(this.factFactory.getNotArg(g, i));
            }
            cArgs.add(this.factFactory.getVarFlag(g));
            Formula<None> isConstant = this.formulaFactory.buildAnd(cArgs);
            Formula<None> eIsConstant = isConstant.evaluate(knownValues);
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            if (eIsConstant != this.ZERO) {
                cArgs.clear();
                cArgs.add(this.factFactory.getVarBot(g));
                cArgs.add(eIsConstant);
                dArgs.add(this.formulaFactory.buildAnd(cArgs));
            }
            NotFormula<None> notFlagG = this.factFactory.getNotFlag(g);
            Formula<None> eNotFlagG = notFlagG.evaluate(knownValues);
            if (eNotFlagG != this.ZERO) {
                ValueCache<None> newValues = knownValues.copy();
                newValues.update(notFlagG);
                cArgs.clear();
                cArgs.add(eNotFlagG);
                cArgs.add(this.encodeDisjunction(s, tApp, OrderRelation.GENGR, newValues));
                dArgs.add(this.formulaFactory.buildAnd(cArgs));
            }
            return this.updateGENGR(stk, vf, this.formulaFactory.buildOr(dArgs));
        }
        // case s=f(t_1, ..., t_n) > t
        TRSFunctionApplication sApp = (TRSFunctionApplication) s;
        FunctionSymbol f = sApp.getRootSymbol();
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        Variable<None> varFlagF = this.factFactory.getVarFlag(f);
        Formula<None> eVarFlagF = knownValues.evaluate(varFlagF);
        if (eVarFlagF != this.ZERO && !t.isVariable()) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(varFlagF);
            // non-collapsing f
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarFlagF);
            TRSFunctionApplication tApp = (TRSFunctionApplication) t;
            cArgs.add(this.encodeGENGRNonCollapsing(s, sApp, t, tApp, newValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return this.updateGENGR(stk, this.ONE, this.ONE);
            }
            args.add(formula);
        }

        // collapsing f
        NotFormula<None> notFlagF = this.factFactory.getNotFlag(f);
        Formula<None> eNotFlagF = notFlagF.evaluate(knownValues);
        if (eNotFlagF != this.ZERO) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(notFlagF);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eNotFlagF);
            cArgs.add(this.encodeConjunction(sApp, t, OrderRelation.GENGR, newValues));
            args.add(this.formulaFactory.buildAnd(cArgs));
        }
        return this.updateGENGR(stk, vf, this.formulaFactory.buildOr(args));
    }

    private Formula<None> updateGENGR(Triple<TRSTerm, TRSTerm, ValueCache<None>> stk, Formula<None> vf, Formula<None> formula) {
        formula = this.formulaFactory.buildAnd(vf, formula);
        this.knownGENGR.put(stk, formula);
        return formula;
    }

    protected abstract Formula<None> encodeGENGRNonCollapsing(TRSTerm s, TRSFunctionApplication sApp, TRSTerm t, TRSFunctionApplication tApp, ValueCache<None> knownValues);

    /**
     * <pre>
% encoding of S>T is "0" in the following cases
%
gt_lpo(S,T,_, 0) :- S==T, !.% opt; need this case only for var(S),var(T)
gt_lpo(S,_,_, 0) :- var(S), !.


% in all other cases it worth memo-ing subresults
%
gt_lpo(W,X,Y,Z) :-
        copy_term([W,X],[A,B]),
        numbervars([A,B],1,_),
        ( lemma_gt_lpo(A,B,Y,Z) ->
            true
        ;
            gt_lpo_work(W,X,Y,Z),
            assertz(lemma_gt_lpo(A,B,Y,Z))
        ).


% encoding of S=f(...)>T  when var(T)
%        Constraint = C1+flag(F)*C2
%

gt_lpo_work(S,T,True,Constraint) :-  nonvar(S), S=..[F|SArgs], var(T), !,
        disjunction(gt,term(F,1,SArgs),term(T),True,C1),
        (C1==1 -> T2=1;
            evaluate(flag(F),True,FlagF),
            (FlagF==0 -> C2=0;
                mysort([flag(F)|True],NewTrue),
                disjunction(eq,term(F,1,SArgs),term(T),NewTrue,C2)
            ),
            simplify(FlagF*C2,T2)
        ),
        simplify(C1+T2,Constraint).

% encoding S=f(s_args)>T=g(t_args)

gt_lpo_work(S,T,True,Constraint) :-   %%% Constraint=not(flag(F))*C1 +
                                 %%%            not(flag(G))*C2 +
                                 %%%            flag(F)*flag(G)*C3
    nonvar(S), nonvar(T), S=..[F|SArgs], T=.. [G|TArgs], !,
    %
    % F is collapsing
    evaluate(not(flag(F)),True,NotFlagF),
    (NotFlagF==0 -> C1=0 ;
        mysort([not(flag(F))|True],NewTrue1),
        conjunction(gt,term(F,1,SArgs),term(T),NewTrue1,C1)
    ),
    simplify(NotFlagF*C1,T1),
    %
    % G is collapsing
    (T1==1 -> T2=1;
        evaluate(not(flag(G)),True,NotFlagG),
        (NotFlagG==0 -> C2=0 ;
            mysort([not(flag(G))|True],NewTrue2),
            conjunction(gt,term(S),term(G,1,TArgs),NewTrue2,C2)
        ),
        simplify(NotFlagG*C2,T2)
    ),
    simplify(T1+T2,Tmp),
    %
    % neither F nor G are collapsing
    (Tmp==1 -> T3=1 ;
        evaluate(flag(F),True,FlagF),
        evaluate(flag(G),True,FlagG),
        simplify(FlagF*FlagG,BothFlags),
        (BothFlags==0 -> C3=0 ;
            sort([flag(F),flag(G)|True],NewTrue3),
            gt_lpo_non_collapsing(S,[F|SArgs],T,[G|TArgs],NewTrue3,C3)
        ),
        simplify(BothFlags*C3,T3)
    ),
    simplify(Tmp+T3,Constraint).
     * </pre>
     * @param s
     * @param t
     * @return
     */
    protected Formula<None> encodeGR(TRSTerm s, TRSTerm t, ValueCache<None> knownValues) {
        Triple<TRSTerm, TRSTerm, ValueCache<None>> stk = new Triple<TRSTerm, TRSTerm, ValueCache<None>>(s,t,knownValues.copy());
        Formula<None> rel = this.knownGR.get(stk);
        if (rel != null) {
            return rel;
        }
        if (s.equals(t)) {
            return this.updateGR(stk, this.ZERO, this.ZERO);
        }
        if (s.isVariable()) {
            //this.knownRelation.put(st, Relation.NGE);
            //the above is wrong for x >= c
            return this.updateGR(stk, this.ZERO, this.ZERO);
        }
        Formula<None> vf = this.encodeVarConstraints(s, t, knownValues);
//      POFormula pf = new POFormula(vf, this.factFactory.getFactMap(), this.formulaFactory, true);
//      System.out.println(s+"\n"+t+"\n"+pf);
        TRSFunctionApplication sApp = (TRSFunctionApplication)s;
        FunctionSymbol f = sApp.getRootSymbol();
        if (t.isVariable()) {
            // case s=f(s_1, ..., s_n) > t
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            Formula<None> formula = this.encodeDisjunction(sApp, t, OrderRelation.GR, knownValues);
            dArgs.add(formula);
            if (formula != this.ONE) {
                Variable<None> varFlagF = this.factFactory.getVarFlag(f);
                Formula<None> eVarFlagF = varFlagF.evaluate(knownValues);
                if (eVarFlagF != this.ZERO) {
                    ValueCache<None> newValues = knownValues.copy();
                    newValues.update(varFlagF);
                    List<Formula<None>> args = new ArrayList<Formula<None>>();
                    args.add(eVarFlagF);
                    args.add(this.encodeDisjunction(sApp, t, OrderRelation.GENGR, newValues));
                    dArgs.add(this.formulaFactory.buildAnd(args));
                }
            }
            return this.updateGR(stk, vf, this.formulaFactory.buildOr(dArgs));
        }
        // case s=f(s_1, ..., s_n) > g(t_1, ..., t_n)=t
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        NotFormula<None> notFlagF = this.factFactory.getNotFlag(f);
        Formula<None> eNotFlagF = notFlagF.evaluate(knownValues);
        if (eNotFlagF != this.ZERO) {
            // f is collapsing
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(notFlagF);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eNotFlagF);
            cArgs.add(this.encodeConjunction(sApp, t, OrderRelation.GR, newValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return this.updateGR(stk, this.ONE, this.ONE);
            }
            args.add(formula);
        }
        TRSFunctionApplication tApp = (TRSFunctionApplication) t;
        FunctionSymbol g = tApp.getRootSymbol();
        Variable<None> varFlagF = this.factFactory.getVarFlag(f);
        Formula<None> eVarFlagF = varFlagF.evaluate(knownValues);
        NotFormula<None> notFlagG = this.factFactory.getNotFlag(g);
        Formula<None> eNotFlagG = notFlagG.evaluate(knownValues);
        if (eVarFlagF != this.ZERO && eNotFlagG != this.ZERO) {
            // f is non-collapsing and g is collapsing
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(varFlagF);
            newValues.update(notFlagG);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarFlagF);
            cArgs.add(eNotFlagG);
            cArgs.add(this.encodeConjunction(s, tApp, OrderRelation.GR, newValues));
            Formula<None> formula = this.formulaFactory.buildAnd(cArgs);
            if (formula == this.ONE) {
                return this.updateGR(stk, this.ONE, this.ONE);
            }
            args.add(formula);
        }
        // non-collapsing f and g
        Variable<None> varFlagG = this.factFactory.getVarFlag(g);
        Formula<None> eVarFlagG = varFlagG.evaluate(knownValues);
        if (eVarFlagF != this.ZERO && eVarFlagG != this.ZERO) {
            ValueCache<None> newValues = knownValues.copy();
            newValues.update(varFlagF);
            newValues.update(varFlagG);
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            cArgs.add(eVarFlagF);
            cArgs.add(eVarFlagG);
            cArgs.add(this.encodeGRNonCollapsing(s, sApp, t, tApp, newValues));
            args.add(this.formulaFactory.buildAnd(cArgs));
        }
        return this.updateGR(stk, vf, this.formulaFactory.buildOr(args));
    }

    private Formula<None> updateGR(Triple<TRSTerm, TRSTerm, ValueCache<None>> stk, Formula<None> vf, Formula<None> formula) {
        formula = this.formulaFactory.buildAnd(vf, formula);
        this.knownGR.put(stk, formula);
        return formula;
    }

    protected abstract Formula<None> encodeGRNonCollapsing(TRSTerm s, TRSFunctionApplication sApp, TRSTerm t, TRSFunctionApplication tApp, ValueCache<None> knownValues);

    protected Formula<None> encodeConjunction(TRSFunctionApplication sApp, TRSTerm t, OrderRelation op, ValueCache<None> knownValues) {
        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
        FunctionSymbol f = sApp.getRootSymbol();
        int fArity = f.getArity();
        List<? extends TRSTerm> si = sApp.getArguments();
        for (int i = 0; i< fArity; i++) {
            Formula<None> formula = this.encodeConjunct(f, i, si.get(i), t, op, knownValues);
            if (formula == this.ZERO) {
                return this.ZERO;
            }
            cArgs.add(formula);
        }
        return this.formulaFactory.buildAnd(cArgs);
    }

    protected Formula<None> encodeConjunction(TRSTerm s, TRSFunctionApplication tApp, OrderRelation op, ValueCache<None> knownValues) {
        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
        FunctionSymbol g = tApp.getRootSymbol();
        int gArity = g.getArity();
        List<? extends TRSTerm> ti = tApp.getArguments();
        for (int i = 0; i< gArity; i++) {
            Formula<None> formula = this.encodeConjunct(g, i, s, ti.get(i), op, knownValues);
            if (formula == this.ZERO) {
                return this.ZERO;
            }
            cArgs.add(formula);
        }
        return this.formulaFactory.buildAnd(cArgs);
    }

    protected Formula<None> encodeConjunction(TRSFunctionApplication sApp, TRSFunctionApplication tApp, OrderRelation op, ValueCache<None> knownValues) {
        List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
        FunctionSymbol f = sApp.getRootSymbol();
        if (Globals.useAssertions) {
            assert f.equals(tApp.getRootSymbol());
        }
        int fArity = f.getArity();
        List<? extends TRSTerm> si = sApp.getArguments();
        List<? extends TRSTerm> ti = tApp.getArguments();
        for (int i = 0; i< fArity; i++) {
            Formula<None> formula = this.encodeConjunct(f, i, si.get(i), ti.get(i), op, knownValues);
            if (formula == this.ZERO) {
                return this.ZERO;
            }
            cArgs.add(formula);
        }
        return this.formulaFactory.buildAnd(cArgs);
    }

    protected Formula<None> encodeConjunct(FunctionSymbol f, int i, TRSTerm s, TRSTerm t, OrderRelation op, ValueCache<None> knownValues) {
        NotFormula<None> notFArgI = this.factFactory.getNotArg(f, i);
        Formula<None> eNotFArgI = notFArgI.evaluate(knownValues);
        if (eNotFArgI == this.ONE) {
            return this.ONE;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(eNotFArgI);
        ValueCache<None> newValues = knownValues.copy();
        Variable<None> varFArgI = this.factFactory.getVarArg(f, i);
        newValues.update(varFArgI);
        switch (op) {
        case GR:
            args.add(this.encodeGR(s, t, newValues));
            break;
        case GE:
            args.add(this.encodeGE(s, t, newValues));
            break;
        case GENGR:
            args.add(this.encodeGENGR(s, t, newValues));
            break;
        default:
            throw new RuntimeException("I only know GR, GE, and GENGR");
        }
        return this.formulaFactory.buildOr(args);
    }

    protected Formula<None> encodeDisjunction(TRSFunctionApplication sApp, TRSTerm t, OrderRelation op, ValueCache<None> knownValues) {
        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        FunctionSymbol f = sApp.getRootSymbol();
        int fArity = f.getArity();
        List<? extends TRSTerm> si = sApp.getArguments();
        for (int i = 0; i< fArity; i++) {
            Formula<None> formula = this.encodeDisjunct(f, i, si.get(i), t, op, knownValues);
            if (formula == this.ONE) {
                return this.ONE;
            }
            dArgs.add(formula);
        }
        return this.formulaFactory.buildOr(dArgs);
    }

    protected Formula<None> encodeDisjunction(TRSTerm s, TRSFunctionApplication tApp, OrderRelation op, ValueCache<None> knownValues) {
        List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
        FunctionSymbol g = tApp.getRootSymbol();
        int gArity = g.getArity();
        List<? extends TRSTerm> ti = tApp.getArguments();
        for (int i = 0; i< gArity; i++) {
            Formula<None> formula = this.encodeDisjunct(g, i, s, ti.get(i), op, knownValues);
            if (formula == this.ONE) {
                return this.ONE;
            }
            dArgs.add(formula);
        }
        return this.formulaFactory.buildOr(dArgs);
    }

    private Formula<None> encodeDisjunct(FunctionSymbol f, int i, TRSTerm s, TRSTerm t, OrderRelation op, ValueCache<None> knownValues) {
        Variable<None> varFArgI = this.factFactory.getVarArg(f, i);
        Formula<None> eVarFArgI = varFArgI.evaluate(knownValues);
        if (eVarFArgI == this.ZERO) {
            return this.ZERO;
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        args.add(eVarFArgI);
        ValueCache<None> newValues = knownValues.copy();
        newValues.update(varFArgI);
        switch (op) {
        case GR:
            args.add(this.encodeGR(s, t, newValues));
            break;
        case GE:
            args.add(this.encodeGE(s, t, newValues));
            break;
        case GENGR:
            args.add(this.encodeGENGR(s, t, newValues));
            break;
        default:
            throw new RuntimeException("I only know GR, GE, and GENGR");
        }
        return this.formulaFactory.buildAnd(args);
    }

    /**
     * <pre>
global(S,N,True,Constraint) :-
        alphabet(S,N,Symbols),
        conjunction_on_symbols(Symbols,Constraint),
        update(Constraint,[],True).

alphabet(S,N,Symbols) :-
        findall(F/I,((member(rule(L,R),S);member(rule(L,R),N)),
                     (T=L;T=R),functorIN(T,F/I)),  List),
        sort(List,Symbols).

functorIN(Term,F/N) :-
    nonvar(Term), functor(Term,F,N).
functorIN(Term,F/N) :-
    nonvar(Term), Term=..[_|Args], member(Arg,Args), functorIN(Arg,F/N).

conjunction_on_symbols([],1) :- !.
conjunction_on_symbols([F/N|Ss],Constraint) :-
    foreach_symbol(F/N,C1),
    conjunction_on_symbols(Ss,C2),
    simplify(C1*C2,Constraint).

foreach_symbol(F/0,flag(F)) :- !.
foreach_symbol(F/N,Constraint) :-
    findall(F/I,between(1,N,I),FIs),
    findall(Conjunction,one_is_true(FIs,Conjunction),List),
    list2disj(List,Disj),
    simplify(flag(F)+Disj,Constraint).

list2disj([],0) :- !.
list2disj([X],X) :- !.
list2disj([X,Y|Xs], X+Conj) :- !, list2disj([Y|Xs],Conj).
     * </pre>
     * @param strict
     * @param nonStrict
     * @param knownValues
     * @return
     */
    public Formula<None> encodeGlobalConstraints(Set<? extends GeneralizedRule> strict, Set<? extends GeneralizedRule> nonStrict, ValueCache<None> knownValues) {
        this.sig = aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(strict);
        if (nonStrict != null) {
            this.sig.addAll(aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(nonStrict));
        }
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        for (FunctionSymbol f : this.sig) {
            if (Globals.DEBUG_NOWONDER) {
                System.err.println("Encoding "+f);
            }
            int arity = f.getArity();
            if (this.noafs) {
                args.add(this.factFactory.getVarFlag(f));
                for (int i = 0; i < arity; i++) {
                    args.add(this.factFactory.getVarArg(f, i));
                }
                continue;
            }
            switch (arity) {
            case 0:
                Variable<None> var = this.factFactory.getVarFlag(f);
                args.add(var);
                if (this.tryStatus) {
                    args.add(this.factFactory.getVarDir(f));
                }
                break;
            case 1:
                // TODO encode that for status to be false at least two arguments must remain
                if (this.tryStatus) {
                    args.add(this.factFactory.getVarDir(f));
                }
            default:
                List<Formula<None>> dArgs = new ArrayList<Formula<None>>();

                if (this.restriction > 0 && this.restriction < arity) {
                    List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
                    cArgs.add(this.factFactory.getVarFlag(f));
                    cArgs.add(this.encodeRestriction(f, this.restriction));
                    dArgs.add(this.formulaFactory.buildAnd(cArgs));
                } else {
                    dArgs.add(this.factFactory.getVarFlag(f));
                }
                dArgs.add(this.patterns.encodeExactlyOne(this.factFactory.getVarArgs(f)));
                args.add(this.formulaFactory.buildOr(dArgs));
            }
        }
        Formula<None> formula = this.formulaFactory.buildAnd(args);
        knownValues.update(formula);
        return formula;
    }

    @Override
    public Afs getAfs(Set<Variable<None>> knownTrue) {
        Afs afs = new Afs();
        for (FunctionSymbol f : this.sig) {
            int arity = f.getArity();
            Variable[] varArgs = this.factFactory.getVarArgs(f);
            if (knownTrue.contains(this.factFactory.getVarFlag(f))) {
                YNM[] args = new YNM[arity];
                for (int i = 0; i < arity; i++) {
                    args[i] = knownTrue.contains(varArgs[i]) ? YNM.YES : YNM.NO;
                }
                afs.setFiltering(f, args);
            } else {
                // f is collapsing
                for (int i = 0; i < arity; i++) {
                    if (knownTrue.contains(varArgs[i])) {
                        afs.setCollapsing(f,i);
                        break;
                    }
                }
            }
        }
        return afs;
    }

    @Override
    public abstract AfsOrder getOrder(Set<Variable<None>> knownTrue, Afs afs);

    public Formula<None> encodeRestriction(FunctionSymbol f, int restriction) {
        RestrictionEncoder re = new RestrictionEncoder(this.formulaFactory);
        Variable<None>[] vars = this.factFactory.getVarArgs(f);
        NotFormula<None>[] nots = this.factFactory.getNotArgs(f);
        return re.encodeRestriction(vars, nots, restriction);
    }

    public class RestrictionEncoder {

        private Variable<None>[] vars;
        private NotFormula<None>[] nots;
        private Stack<Boolean> stack;
        private List<Formula<None>> list;
        private int restriction;
        private FormulaFactory<None> formulaFactory;

        public RestrictionEncoder(FormulaFactory<None> formulaFactory) {
            this.formulaFactory = formulaFactory;
        }

        public Formula<None> encodeRestriction(Variable<None>[] vars, NotFormula<None>[] nots, int restriction) {
            this.list = new ArrayList<Formula<None>>();
            this.stack = new Stack<Boolean>();
            this.vars = vars;
            this.nots = nots;
            this.restriction = restriction;
            this.encode(0, 0);
            return this.formulaFactory.buildAnd(this.list);
        }

        private void encode(int i, int selected) {
            if (i == this.vars.length) {
                List<Formula<None>> left = new ArrayList<Formula<None>>();
                List<Formula<None>> right = new ArrayList<Formula<None>>();
                for (int j = 0; j < i; j++) {
                    if (this.stack.get(j) == Boolean.TRUE) {
                        left.add(this.vars[j]);
                    } else {
                        right.add(this.nots[j]);
                    }
                }
                List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
                dArgs.add(this.formulaFactory.buildNot(this.formulaFactory.buildAnd(left)));
                dArgs.add(this.formulaFactory.buildAnd(right));
                this.list.add(this.formulaFactory.buildOr(dArgs));
            } else {
                if (selected < this.restriction) {
                    this.stack.push(Boolean.TRUE);
                    this.encode(i+1, selected+1);
                    this.stack.pop();
                }
                if (i-selected < this.vars.length-this.restriction) {
                    this.stack.push(Boolean.FALSE);
                    this.encode(i+1, selected);
                    this.stack.pop();
                }
            }
        }

    }

    @Override
    public boolean isAllowQuasi() {
        return this.allowQuasi;
    }

    public Formula<None> encodeVarConstraints(TRSTerm s, TRSTerm t,  ValueCache<None> knownValues) {
        List<Formula<None>> args = new ArrayList<Formula<None>>();
        Map<aprove.verification.dpframework.BasicStructures.TRSVariable, List<List<Formula<None>>>> sMap = this.getVarMap(s);
        Map<aprove.verification.dpframework.BasicStructures.TRSVariable, List<List<Formula<None>>>> tMap = this.getVarMap(t);
        for (Map.Entry<aprove.verification.dpframework.BasicStructures.TRSVariable, List<List<Formula<None>>>> entry : tMap.entrySet()) {
            aprove.verification.dpframework.BasicStructures.TRSVariable tVar = entry.getKey();
            List<Formula<None>> dArgs = new ArrayList<Formula<None>>();
            List<Formula<None>> cArgs = new ArrayList<Formula<None>>();
            for (List<Formula<None>> pos : entry.getValue()) {
                cArgs.add(this.formulaFactory.buildNot(this.formulaFactory.buildAnd(pos)));
            }
            dArgs.add(this.formulaFactory.buildAnd(cArgs));
            List<List<Formula<None>>> sPoss = sMap.get(tVar);
            if (sPoss != null) {
                for (List<Formula<None>> pos : sPoss) {
                    dArgs.add(this.formulaFactory.buildAnd(pos));
                }
            }
            args.add(this.formulaFactory.buildOr(dArgs));
        }
        return this.formulaFactory.buildAnd(args).evaluate(knownValues);
    }

    private Map<aprove.verification.dpframework.BasicStructures.TRSVariable, List<List<Formula<None>>>> getVarMap(TRSTerm t) {
        Map<aprove.verification.dpframework.BasicStructures.TRSVariable, List<List<Formula<None>>>> map = new LinkedHashMap<aprove.verification.dpframework.BasicStructures.TRSVariable, List<List<Formula<None>>>>();
        List<Formula<None>> pos = new ArrayList<Formula<None>>();
        this.getVarMap(t, map, pos);
        return map;
    }

    private void getVarMap(TRSTerm t, Map<aprove.verification.dpframework.BasicStructures.TRSVariable, List<List<Formula<None>>>> map, List<Formula<None>> pos) {
        if (t.isVariable()) {
            aprove.verification.dpframework.BasicStructures.TRSVariable var = (aprove.verification.dpframework.BasicStructures.TRSVariable) t;
            List<List<Formula<None>>> poss = map.get(var);
            if (poss == null) {
                poss = new ArrayList<List<Formula<None>>>();
                map.put(var, poss);
            }
            poss.add(new ArrayList<Formula<None>>(pos));
        } else {
            TRSFunctionApplication fApp = (TRSFunctionApplication) t;
            List<? extends TRSTerm> args = fApp.getArguments();
            FunctionSymbol f = fApp.getRootSymbol();
            int arity = f.getArity();
            if (Globals.useAssertions) {
                assert(arity == args.size());
            }
            Variable<None>[] varArgs = this.factFactory.getVarArgs(f);
            for (int i = 0; i < arity; i++) {
                pos.add(varArgs[i]);
                this.getVarMap(args.get(i), map, pos);
                pos.remove(pos.size()-1);
            }
        }
    }
}
