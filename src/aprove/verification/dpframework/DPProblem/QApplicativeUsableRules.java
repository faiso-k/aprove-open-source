package aprove.verification.dpframework.DPProblem;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.ValueCaches.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * Can be used for A-transformations of all kinds
 * (DP-problems, TRSs, constraints, etc.)
 *
 * @author thiemann
 * @version $Id$
 */
public class QApplicativeUsableRules {

    /**
     * Checks whether all symbols in the given rules are in applicative form.
     */
    public static boolean applicativeRules(Iterable<Rule> R) {
        return QApplicativeUsableRules.applicativeSignature(aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(R));
    }

    /**
     * Checks whether fs is an applicative signature, i.e. only contains
     * constants and binary symbols.
     * @param fs
     */
    public static boolean applicativeSignature(Iterable<FunctionSymbol> fs) {
        for (FunctionSymbol f : fs) {
            int ar = f.getArity();
            if (ar != 0 && ar != 2) {
                return false;
            }
        }
        return true;
    }

    //  we have the possibility to specialize usable-rules conditions for subterms when it
    // is detected that a rule is already usable on top-level and then one can replace the usedFlags by true,
    //  but perhaps the overhead is not worth the possibly simpler formula
    static final boolean specialize = true;

    /*
     * some sharable static things
     */
    private final static Set<Rule> emptyRules = new HashSet<Rule>(0);
    private final static Map<FunctionSymbol,Set<Integer>> emptyArityMap = new HashMap<FunctionSymbol,Set<Integer>>(0);
    private static final TRSFunctionApplication dummy =
        TRSTerm.createFunctionApplication(FunctionSymbol.create("notProper", 0), TRSTerm.EMPTY_ARGS);
    private static final Rule dummyRule = Rule.create(QApplicativeUsableRules.dummy, QApplicativeUsableRules.dummy);


    /*
     * the real attributes
     */
    private final Map<List<FunctionSymbol>, FunctionSymbol> applToFuncSignature; // the map from f''# and f''' into functional signature
    private final Set<FunctionSymbol> funcSignature; // equiv to applToFuncSignature(values), used to avoid name clashes


    private final boolean innermost;
    private final QTermSet Q;
    private final Map<Rule, State> stateMap;
    private final Map<Rule, DpState> dpStateMap;
    private final Map<FunctionSymbol, Set<Rule>> R; // a mapping from function symbols to corresponding rules, repr. R
                                               // here f is the f in f't1'..'tn -> r
                                               // and a key null is for the rules x't1'..'tn -> r

    private Map<FunctionSymbol, Integer> Qarities; // a mapping for the arities of Q, null, if Q is not proper
    private final QTermSet aTransQ;  // the aTransformedQ or null, if Q is not proper

    /*
     * for encoding to formulae over properties
     */
    private final FormulaFactory<Property> ffactory;
    private final Formula<Property> ff;
    private final Formula<Property> tt;


    /**
     * Create an QApplicativeUsableRules object, may only be called if the signature
     * of the qtrs is applicative, i.e. all occurring symbols must have arity 0 or 2!
     * @param qtrs
     */
    public QApplicativeUsableRules(QTRSProblem qtrs) {
        if (Globals.useAssertions) {
            assert(QApplicativeUsableRules.applicativeSignature(qtrs.getSignature()));
        }
        int sigSize = qtrs.getSignature().size();
        this.funcSignature = new HashSet<FunctionSymbol>(sigSize+5);
        this.funcSignature.add(QApplicativeUsableRules.dummy.getRootSymbol());
        this.applToFuncSignature = new HashMap<List<FunctionSymbol>, FunctionSymbol>(sigSize);
        Set<Rule> R = qtrs.getR();
        this.Q = qtrs.getQ();
        this.innermost = qtrs.QsupersetOfLhsR();
        this.R = new HashMap<FunctionSymbol, Set<Rule>>();

        this.stateMap = new LinkedHashMap<Rule, State>(R.size());
        this.dpStateMap = new HashMap<Rule, DpState>();

        this.ffactory = new FullSharingFlatteningFactory<Property>();
        this.ff = this.ffactory.buildConstant(false);
        this.tt = this.ffactory.buildConstant(true);

        // first build all states, as some info in states of all rules
        // is required when encoding the first rule. (e.g. the usable flags)
        FunctionSymbol xf;
        int ruleCount = 1;
        for (Rule rule : R) {
            this.stateMap.put(rule, new State(rule, this.ffactory.buildTheoryAtom(new UsableProp(rule, ruleCount++))));
            TRSTerm root = QApplicativeUsableRules.partition(rule.getLeft()).x;
            if (root.isVariable()) {
                xf = null;
            } else {
                xf = ((TRSFunctionApplication)root).getRootSymbol();
            }
            Set<Rule> xfRules = this.R.get(xf);
            if (xfRules == null) {
                xfRules = new HashSet<Rule>();
                this.R.put(xf, xfRules);
            }
            xfRules.add(rule);
        }
        // now do the real encoding.
        for (State state : this.stateMap.values()) {
            this.encodeProperAndUsable(state);
        }

        this.aTransQ = this.aTransformQ(this.Q);
    }

    /**
     * gets (and if necessary adds) the state for the given dp
     * @param dp
     * @return
     */
    private DpState getDP(Rule dp) {
        DpState state = this.dpStateMap.get(dp);
        if (state == null) {
            state = new DpState(dp);
            this.dpStateMap.put(dp, state);
            this.encodeProperAndUsableDP(state);
            if (Globals.DEBUG_THIEMANN) {
                System.out.println(state);
            }
        }
        return state;
    }


    /**
     * computes the active constraints for a given set of DPs,
     * null is returned, if the DP problem cannot be pi-proper regardless of pi.
     * @param P a set of DPs only containing constant and binary symbols!
     * @return the quadruple containing
     *  1) the map from DPs to a-transformed DPs
     *  2) the map from a usable rule to a-transformed usable rule together with a variable used_rule
     *  3) a formula to ensure pi-proper arities and to ensure that the used_rule variables are accordingly set
     *  4) a flag which says whether the DPs are preprocessed by an argument filter pi which replaces every
     *     binary head symbol by its second argument (for that reason the a-transformed DPs are just pair-terms and not rules)
     */
    public synchronized Quadruple<Map<Rule,Pair<TRSTerm, TRSTerm>>, Map<Rule, Pair<GeneralizedRule,Variable<AfsProp>>>, Formula<AfsProp>, Boolean> getDPConstraints(Set<Rule> P, Set<FunctionSymbol> headSyms) {
        if (Globals.useAssertions) {
            assert(QApplicativeUsableRules.applicativeRules(P));
        }
        int n = P.size();
        int m = this.stateMap.size();
        List<Formula<Property>> phi = new ArrayList<Formula<Property>>(n+m);
        Map<FunctionSymbol, Set<Integer>> arities = new HashMap<FunctionSymbol, Set<Integer>>();
        Map<Rule, Pair<TRSTerm, TRSTerm>> dpToADP = new LinkedHashMap<Rule, Pair<TRSTerm, TRSTerm>>(n);
        List<State> todo = new ArrayList<State>(n);

        boolean second = false;

        // init the DPs
        for (Rule dp : P) {
            DpState dpState = this.getDP(dp);
            Formula<Property> phii = dpState.phi;
            if (phii == this.ff) {
                // conflict, so we can try to filter the tuple symbols to second argument
                dpToADP.clear();
                todo.clear();
                phi.clear();
                arities.clear();
                second = true;
                break;
            }

            todo.add(dpState);
            phi.add(phii);
            dpState.mergeArities(arities);
            dpToADP.put(dp, new Pair<TRSTerm, TRSTerm>(dpState.aRule.getLeft(), dpState.aRule.getRight()));
        }

        if (second) {
            for (Rule dp : P) {
                DpState dpState = this.getDP(dp);
                YNM secPossible = dpState.getSecond(headSyms);
                if (secPossible.isBool()) {
                    second = secPossible.toBool();
                } else {
                    // we have a problem with the sides, as one side has binary app head symbol and the
                    // other has binary app non-head symbol
                    return null;
                }
                Formula<Property> phii = dpState.getSecondPhi(second);
                if (phii == this.ff) {
                    // conflict
                    return null;
                }

                todo.add(dpState);
                phi.add(phii);
                dpState.mergeSecondArities(arities, second);
                dpToADP.put(dp, dpState.getSecondARule(second));
            }
            second = true;
        }

        Set<State> have = new HashSet<State>(n+m);
        List<State> newTodo = new ArrayList<State>();

        // orig rule to (atransRule, PL-Variable)
        final Map<Rule, Pair<GeneralizedRule,Variable<AfsProp>>> usableMap = new HashMap<Rule, Pair<GeneralizedRule,Variable<AfsProp>>>(m);

        final FormulaFactory<AfsProp> afsEncoder = new FullSharingFlatteningFactory<AfsProp>();

        // now perform the usable rules closure
        // and create the propositional variables for the used-flags
        while (!todo.isEmpty()) {
            for (State state : todo) {
                Set<Rule> usable = state instanceof DpState
                        ? ((DpState)state).getSecondUsable(second)
                        : state.usableRules;
                for (Rule rule : usable) {

                    State usedState = this.stateMap.get(rule);
                    if (have.add(usedState)) {
                        usedState.mergeArities(arities);
                        phi.add(this.ffactory.buildImplication(usedState.usedFlag, usedState.phi));
                        usableMap.put(usedState.rule, new Pair<GeneralizedRule, Variable<AfsProp>>(usedState.aRule, afsEncoder.buildVariable()));
                        newTodo.add(usedState);
                    }
                }
            }

            // swap todo and newTodo
            List<State> oldTodo = todo;
            todo = newTodo;
            newTodo = oldTodo;

            newTodo.clear();

        }


        // and build final formula (still containing theory atoms)
        final Formula<Property> preFinalPhi = this.ffactory.buildAnd(phi);


        //
        // at this step we have to replace the theory atoms, i.e.
        // essentially we have to construct the arity constraints that
        // only one arity may be chosen.
        //
        // This we do by a log-encoding, e.g. if ar(f) in {1,2,6} then
        // we replace ar(f) = 1 by X and Y
        //            ar(f) = 2 by X and not Y
        // and        ar(f) = 6 by not X and Y
        //
        // so we first have to come up with this encodings
        // and then replace the theory atoms by their encodings
        //

        final Formula<AfsProp> tt = afsEncoder.buildConstant(true);

        // store for each f and i how to encode "f has arity i".
        final Map<FunctionSymbol,Map<Integer,Formula<AfsProp>>> extArities = new HashMap<FunctionSymbol,Map<Integer,Formula<AfsProp>>>(arities.size());

        for (Map.Entry<FunctionSymbol, Set<Integer>> arityEntry : arities.entrySet()) {
            Set<Integer> possArities = arityEntry.getValue();
            final int size = possArities.size();
            if (Globals.useAssertions) {
                assert(size >= 1);
            }

            Map<Integer,Formula<AfsProp>> encodings = new HashMap<Integer,Formula<AfsProp>>(size);

            // special handling for cases for 1 and 2 for speed
            if (size == 1) {
                encodings.put(possArities.iterator().next(), tt);
            } else if (size == 2) {
                Iterator<Integer> i = possArities.iterator();
                Variable<AfsProp> newVar = afsEncoder.buildVariable();
                encodings.put(i.next(), newVar);
                encodings.put(i.next(), afsEncoder.buildNot(newVar));
            } else {

                // how many bits do we need?
                int bits = 0;
                for (int i = size-1; i != 0; bits++) {
                    i >>= 1;
                }

                // okay, let us encode in bit-vectors
                Variable<AfsProp>[] vars = new Variable[bits];
                Formula<AfsProp>[] negVars = new Formula[bits];
                for (int i=0; i<bits; i++) {
                    Variable<AfsProp> var = afsEncoder.buildVariable();
                    vars[i] = var;
                    negVars[i] = afsEncoder.buildNot(var);
                }

                int currentEncoding = 0;
                List<Formula<AfsProp>> bitCombination = new ArrayList<Formula<AfsProp>>(bits);
                for (Integer integer : possArities) {
                    int currentTester = 1;
                    for (int i=0; i<bits; i++) {
                        if ((currentEncoding & currentTester) == currentTester) {
                            bitCombination.add(negVars[i]);
                        } else {
                            bitCombination.add(vars[i]);
                        }
                        currentTester <<= 1;
                    }
                    encodings.put(integer, afsEncoder.buildAnd(bitCombination));
                    currentEncoding++;
                    bitCombination.clear();
                }
            }
            // finally store our encodings;
            extArities.put(arityEntry.getKey(), encodings);
        }

        //
        // now we know how to encode "a rule is usable" and "the arity of f is i"
        // let us now remove all theory atoms except the "pi regards its i-th argument"
        //

        TheoryConverter<Property,AfsProp> converter = new TheoryConverter<Property,AfsProp>() {

            @Override
            public Formula<AfsProp> convert(Property theoryProp) {
                if (theoryProp instanceof UsableProp) {
                    UsableProp uProp = (UsableProp) theoryProp;
                    return usableMap.get(uProp.rule).y;
                } else if (theoryProp instanceof ArityProp) {
                    ArityProp arProp = (ArityProp) theoryProp;
                    return extArities.get(arProp.f).get(arProp.arity);
                } else if (theoryProp instanceof AfsProp) {
                    return afsEncoder.buildTheoryAtom((AfsProp) theoryProp);
                } else {
                    throw new RuntimeException("Unknown property type: "+theoryProp.getClass());
                }
            }

        };


        Formula<AfsProp> finalPhi = preFinalPhi.apply(new TheoryConverterVisitor<Property,AfsProp>(afsEncoder,converter));

        /*
         * start debug out
         */
        if (Globals.DEBUG_THIEMANN) {
            System.out.println("The DPs:");
            for (Map.Entry<Rule,Pair<TRSTerm,TRSTerm>> dp : dpToADP.entrySet()) {
                System.out.println("  "+dp.getKey() +  "  ----A--->  "+dp.getValue().x + " -> "+dp.getValue().y);
            }

            System.out.println("\nThe usable rules:");
            for (Map.Entry<Rule, Pair<GeneralizedRule,Variable<AfsProp>>> rule : usableMap.entrySet()) {
                System.out.println("  "+rule.getValue().y+": "+rule.getKey()+"  ----A--->  "+rule.getValue().x);
            }

            System.out.println("\nThe pre-final-formula is\n  "+preFinalPhi);
            System.out.println("\nThe final     formula is\n  "+finalPhi);
        }
        /*
         * end debug out
         */

        return new Quadruple<Map<Rule,Pair<TRSTerm, TRSTerm>>, Map<Rule, Pair<GeneralizedRule,Variable<AfsProp>>>, Formula<AfsProp>, Boolean>(dpToADP, usableMap, finalPhi, second);
    }


    /**
     * computes the set of a-transformed pairs and rules
     * provided that P and R are proper (for P a mapping of original to a-transformed rules is returned).
     * null is returned otherwise.
     * @param P a set of DPs only containing constants and binary function symbols
     * @param R - note that R can be a subset of the internally stored QTRS. This is needed, as one can take usable rules
     *             without creating a new instance of this class. Then the internally stored TRS and R do not coincide any more.
     */
    public synchronized Pair<Map<Rule,Rule>, Map<Rule,Rule>> getATransformedPR(Collection<Rule> P, Collection<Rule> R) {
        if (Globals.useAssertions) {
            assert(QApplicativeUsableRules.applicativeRules(P));
            assert(this.stateMap.keySet().containsAll(R));
        }
        Map<Rule,Rule> rules = new LinkedHashMap<Rule,Rule>(R.size());
        Map<FunctionSymbol, Integer> arities = new HashMap<FunctionSymbol, Integer>();
        Collection<State> todo = new ArrayList<State>(R.size());
        for (Rule rule : R) {
            todo.add(this.stateMap.get(rule));
        }

        if (this.getATransformedRules(rules, arities, todo)) {
            // R is okay, and rules contains a-transformed R
            // so lets transform P
            Map<Rule,Rule> aP = new LinkedHashMap<Rule,Rule>(P.size());

            for (Rule dp : P) {
                State dpState = this.getDP(dp);
                if (dpState.mergeProperArity(arities)) {
                    // as P is proper all a-transformed rules satisfy variable condition
                    aP.put(dp, Rule.fromGeneralizedRule(dpState.aRule));
                } else {
                    // dp is not proper or has a conflict in arities
                    return null;
                }
            }
            return new Pair<Map<Rule,Rule>,Map<Rule,Rule>>(aP, rules);
        } else {
            // conflict in R already
            return null;
        }
    }



    /**
     * computes the set of a-transformed dps (a mapping from old DPs to a-transformed DPs)
     * and the a-transformed qtrs, provided that P cup R cup Q is proper;
     * null is returned otherwise.
     * @param P a set of DPs only containing constants and binary function symbols
     * @param R - note that R can be a subset of the internally stored QTRS. This is needed, as one can take usable rules
     *             without creating a new instance of this class. Then the internally stored TRS and R do not coincide any more.
     */
    public synchronized Pair<Map<Rule,Rule>, QTRSProblem> getATransformedQDP(Set<Rule> P, Set<Rule> R) {
        if (Globals.useAssertions) {
            assert(QApplicativeUsableRules.applicativeRules(P));
            assert(this.stateMap.keySet().containsAll(R));
        }
        Pair<QTRSProblem, Map<FunctionSymbol, Integer>> qtrsAndArity = this.getATransformedQTRS(R);
        if (qtrsAndArity == null) {
            return null;
        } else {
            Map<Rule,Rule> aP = new LinkedHashMap<Rule,Rule>(P.size());
            Map<FunctionSymbol, Integer> arities = qtrsAndArity.y;
            for (Rule dp : P) {
                State dpState = this.getDP(dp);
                if (dpState.mergeProperArity(arities)) {
                    // as P is proper we know that aRule satisfies var-condition
                    aP.put(dp,Rule.fromGeneralizedRule(dpState.aRule));
                } else {
                    // dp is not proper or has a conflict in arities
                    return null;
                }
            }
            return new Pair<Map<Rule,Rule>,QTRSProblem>(aP, qtrsAndArity.x);
        }
    }


    /**
     * delivers the QTRS (A(R),A(Q)) and the according arities, if Q cup R is proper;
     * null, if Q cup R is not proper
     * @param R - note that R can be a subset of the internally stored QTRS. This is needed, as one can take usable rules
     *             without creating a new instance of this class. Then the internally stored TRS and R do not coincide any more.
     */
    public synchronized Pair<QTRSProblem, Map<FunctionSymbol, Integer>> getATransformedQTRS(Set<Rule> R) {
        if (Globals.useAssertions) {
            assert(this.stateMap.keySet().containsAll(R));
        }
        if (this.aTransQ == null) {
            return null;
        } else {
            Map<FunctionSymbol, Integer> arities = new HashMap<FunctionSymbol, Integer>(this.Qarities);
            Set<Rule> atrans = new LinkedHashSet<Rule>();

            for (Rule rule : R) {
                State state = this.stateMap.get(rule);
                if (state.mergeProperArity(arities)) {
                    // note that as we require properness we know that the aRule satisfied variable condition
                    atrans.add(Rule.fromGeneralizedRule(state.aRule));
                } else {
                    // oops, have a conflict or a non-proper rule
                    return null;
                }
            }
            QTRSProblem aQtrs = QTRSProblem.create(ImmutableCreator.create(atrans), this.aTransQ);
            return new Pair<QTRSProblem, Map<FunctionSymbol, Integer>>(aQtrs, arities);
        }
    }

    /**
     * adds the a-transformed verions of all proper rules reachable by todo-states into rules
     *
     * @param rules the a-transformed rules are added here, will be modified
     * @param arities the initial restriction on arities, will be modified
     * @param todo the set of states that should be used as starting point, will be modified
     * @return false iff we encountered some inproper-rule or an arity-conflict, then the set rules is unspecified.
     *          true if there was no problem and to rules all a-transformed rules are added
     */
    private boolean getATransformedRules(Map<Rule,Rule> rules, Map<FunctionSymbol, Integer> arities, Collection<State> todo) {
        Set<State> have = new HashSet<State>(todo);

        Collection<State> newTodo = new ArrayList<State>();

        while (!todo.isEmpty()) {

            for (State state : todo) {
                if (!state.mergeProperArity(arities)) {
                    // oops, have a conflict or a non-proper rule
                    return false;
                }

                rules.put(state.rule,Rule.fromGeneralizedRule(state.aRule));

                for (Rule rule : state.usableRules) {
                    State usedState = this.stateMap.get(rule);
                    if (have.add(usedState)) {
                        newTodo.add(state);
                    }
                }
            }

            // swap todo and newTodo
            Collection<State> oldTodo = todo;
            todo = newTodo;
            newTodo = oldTodo;

            newTodo.clear();

        }

        return true;
    }

    /**
     * determines the arities for Q and the A-transformed Q-terms,
     * returns null, if Q is not proper or the a-transformed Q,
     * the arities are store in the latter case in the corresponding attribute
     * of this
     */
    private QTermSet aTransformQ(QTermSet Q) {
        State state = new State(null,null);
        state.arities = new HashMap<FunctionSymbol, Set<Integer>>();
        state.properArities = new HashMap<FunctionSymbol, Integer>();
        Triple<Formula<Property>, TRSTerm, TRSTerm> result =
            new Triple<Formula<Property>, TRSTerm, TRSTerm>(null, null, null);

        Map<FunctionSymbol, Integer> arityMap = new HashMap<FunctionSymbol, Integer>();
        Set<Pair<FunctionSymbol,Integer>> afs = new HashSet<Pair<FunctionSymbol,Integer>>();

        Set<TRSFunctionApplication> atransQ = new LinkedHashSet<TRSFunctionApplication>();

        for (TRSFunctionApplication ft : Q.getTerms()) {
            this.encodeProper(result, ft, arityMap, afs, state, null);
            if (state.properArities == null) {
                // we have detected inconsistence
                return null;
            } else {
                atransQ.add((TRSFunctionApplication)result.y);
            }
        }

        this.Qarities = state.properArities;
        return new QTermSet(atransQ);
    }


    /**
     * partitions a term x '1 t_1 '2 ... 'n t_n into <x, ['1,'2,..,'n], [t_1,...,t_n]>
     * @param t
     * @return
     */
    private static Triple<TRSTerm, FunctionSymbol[], TRSTerm[]> partition(TRSTerm t) {
        if (t.isVariable()) {
            return new Triple<TRSTerm, FunctionSymbol[], TRSTerm[]>(t, new FunctionSymbol[0], new TRSTerm[0]);
        } else {
            int n = 0;
            TRSTerm s = t;
            TRSFunctionApplication fs = (TRSFunctionApplication) t;
            FunctionSymbol f = fs.getRootSymbol();
            while (f.getArity() == 2) {
                n++;
                s = fs.getArgument(0);
                if (s.isVariable()) {
                    break;
                } else {
                    fs = (TRSFunctionApplication) s;
                    f = fs.getRootSymbol();
                }
            }

            if (Globals.useAssertions) {
                assert(f.getArity() == 0 || f.getArity() == 2);
            }
            // now we have the arity and the left-most symbol
            FunctionSymbol[] apSyms = new FunctionSymbol[n];
            TRSTerm[] args = new TRSTerm[n];

            while (n > 0) {
                n--;
                fs = (TRSFunctionApplication) t;
                apSyms[n] = fs.getRootSymbol();
                args[n] = fs.getArgument(1);
                t = fs.getArgument(0);
            }
            if(Globals.useAssertions) {
                assert (t.equals(s));
            }
            return new Triple<TRSTerm, FunctionSymbol[], TRSTerm[]>(s, apSyms, args);
        }
    }

    /**
     * modifies the state that says: I'm not pi-proper regardless of pi.
     * @param state
     */
    private void setDefinitelyInproper(State state) {
        state.properArities = null;
        state.aRule = QApplicativeUsableRules.dummyRule;
        state.phi = this.ff;
        state.usableRules = QApplicativeUsableRules.emptyRules;
        state.arities = QApplicativeUsableRules.emptyArityMap;
    }


    /**
     * encode for a given state rule of a rule that it is proper and that its
     * usable rules are regarded.
     * @param state
     */
    private void encodeProperAndUsable(State state) {
        final Rule rule = state.rule;
        final Map<FunctionSymbol,Integer> arities;

        final TRSTerm left = rule.getLeft();


        // first try to determine the outermost arities for left- and right-hand-sides
        Triple<TRSTerm, FunctionSymbol[], TRSTerm[]> partition = QApplicativeUsableRules.partition(left);
        if (partition.x.isVariable()) {
            // waw, inproper on top-level
            if (Globals.useAssertions) {
                assert(partition.y.length != 0);
            }
            this.setDefinitelyInproper(state);
            return;
        } else {
            arities = new HashMap<FunctionSymbol, Integer>();
            arities.put(((TRSFunctionApplication)partition.x).getRootSymbol(), partition.y.length);
        }

        final TRSTerm right = rule.getRight();


        partition = QApplicativeUsableRules.partition(right);
        if (partition.x.isVariable()) {
            if (partition.y.length != 0) {
                // waw, rhs = x ' .. ' t_n with n > 0
                this.setDefinitelyInproper(state);
                return;
            }
        } else {
            int ar = partition.y.length;
            Integer oldArity = arities.put(((TRSFunctionApplication)partition.x).getRootSymbol(), ar);
            if (oldArity != null && oldArity.intValue() != ar) {
                // we have an arity clash on top-level
                this.setDefinitelyInproper(state);
                return;
            }
        }

        // okay, now we have to really encode
        // so first init some more required sets/maps/...
        final Set<Pair<FunctionSymbol,Integer>> afs = new HashSet<Pair<FunctionSymbol,Integer>>();
        state.arities = new HashMap<FunctionSymbol, Set<Integer>>();
        state.properArities = new HashMap<FunctionSymbol, Integer>();

        Triple<Formula<Property>, TRSTerm, TRSTerm> result =
            new Triple<Formula<Property>, TRSTerm, TRSTerm>(null, null, null);

        List<Formula<Property>> conjuncts =
            new ArrayList<Formula<Property>>(4);

        // the arities on top-level
        for (Map.Entry<FunctionSymbol, Integer> arityEntry : arities.entrySet()) {
            conjuncts.add(this.getPropForArity(state, arityEntry.getKey(), arityEntry.getValue()));
        }

        // lhs
        this.encodeProper(result, left, arities, afs, state, null);
        final TRSFunctionApplication aLeft = (TRSFunctionApplication) result.y;
        conjuncts.add(result.x);


        // and rhs
        Rule renamedRule = rule.getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
        // first compute the set S, stored in array for more efficient iteration
        TRSTerm[] Sarr;

        // S = {l1,..,ln} for rule f(l1,..,ln) -> r
        Collection<? extends TRSTerm> args = renamedRule.getLeft().getArguments();
        Set<TRSTerm> S = new HashSet<TRSTerm>(args.size()); // calculate S

        // TODO: throw out variables as these will never lead to a clash (true?)
        for (TRSTerm arg : args) {
            if (!arg.isVariable()) {
                S.add(arg);
            }
        }
        Sarr = new TRSTerm[S.size()];
        S.toArray(Sarr);

        // now get renamed rhs and matcher for orig rhs (to build a-transformed rhs correctly)
        // (we do not work fully on the renamed rule as then the a-transformed rule which
        //  is presented to the user is variable renamed)
        final int firstFreeNr = 0;
        TRSTerm renamedRight = renamedRule.getRight();
        TRSSubstitution renaming = renamedRight.getMatcher(right);
        this.encodeProperAndUsable(result, rule, renamedRight, firstFreeNr, Sarr, arities, afs, state, null);
        final TRSTerm aRight = result.y.applySubstitution(renaming);
        conjuncts.add(result.x);

        state.phi = this.ffactory.buildAnd(conjuncts);
        state.aRule = GeneralizedRule.create(aLeft, aRight);
        return;
    }

    private void encodeProperAndUsableDP(DpState state) {
        final Rule rule = state.rule;
        final Map<FunctionSymbol,Integer> arities = new HashMap<FunctionSymbol,Integer>();

        Triple<Formula<Property>, TRSTerm, TRSTerm> result =
            new Triple<Formula<Property>, TRSTerm, TRSTerm>(null, null, null);

        final Set<Pair<FunctionSymbol,Integer>> afs = new HashSet<Pair<FunctionSymbol,Integer>>();

        // first consider lhs;
        final TRSFunctionApplication left = rule.getLeft();

        FunctionSymbol f = left.getRootSymbol();

        // should we consider the second argument of lhs separately, i.e.
        // should we apply an AF on outermost tuple-symbol
        boolean considerSecondArg = f.getArity() == 2;

        state.arities = new HashMap<FunctionSymbol, Set<Integer>>();
        state.properArities = new HashMap<FunctionSymbol, Integer>();

        this.encodeProper(result, left, arities, afs, state, considerSecondArg ? state : null);

        final TRSFunctionApplication aLeft = (TRSFunctionApplication) result.y;
        state.phi = result.x;


        if (!considerSecondArg) {
            // if we have not consider the second argument of lhs separately, then
            // copy the state-result as second-result
            state.secondPhi = state.phi;
            state.secondALeft = aLeft;
            state.secondArities = QApplicativeUsableRules.copyArityMap(state.arities);
        }


        // now consider the right hand side
        final TRSTerm right = rule.getRight();

        considerSecondArg = !right.isVariable() && ((TRSFunctionApplication)right).getRootSymbol().getArity() == 2;

        Rule renamedRule = rule.getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
        // first compute the set S, stored in array for more efficient iteration
        TRSTerm[] Sarr = new TRSTerm[]{renamedRule.getLeft()};

        // now get renamed rhs and matcher for orig rhs (to build a-transformed rhs correctly)
        // (we do not work fully on the renamed rule as then the a-transformed rule which
        //  is presented to the user is variable renamed)
        final int firstFreeNr = 0;
        TRSTerm renamedRight = renamedRule.getRight();
        TRSSubstitution renaming = renamedRight.getMatcher(right);
        this.encodeProperAndUsable(result, null, renamedRight, firstFreeNr, Sarr, arities, afs, state, considerSecondArg ? state : null);
        final TRSTerm aRight = result.y.applySubstitution(renaming);
        state.phi = this.ffactory.buildAnd(state.phi, result.x);
        if (!considerSecondArg) {
            state.secondPhi = this.ffactory.buildAnd(state.secondPhi, result.x);
            state.secondARight = aRight;
            state.secondUsableRules = state.usableRules;
        } else {
            state.secondARight = state.secondARight.applySubstitution(renaming);
        }

        state.aRule = GeneralizedRule.create(aLeft, aRight);
        return;
    }

    private static Map<FunctionSymbol, Set<Integer>> copyArityMap(Map<FunctionSymbol, Set<Integer>> arities) {
        Map<FunctionSymbol, Set<Integer>> copy = new HashMap<FunctionSymbol, Set<Integer>>(arities.size());
        for (Map.Entry<FunctionSymbol, Set<Integer>> entry : arities.entrySet()) {
            copy.put(entry.getKey(), new TreeSet<Integer>(entry.getValue()));
        }
        return copy;
    }

    /**
     * Encodes that a term t is pi-proper and returns additionally the
     * a-transformed term. Those parts that are not proper (and hence cannot be
     * transformed by a-transformation) are replaced by the dummy-term.
     * The third part of the result can be ignored.
     * If headDP is set to true, then we also compute the state for the second
     * argument of t.
     * @param result - put the formula and the a-transformed term here.
     * @param t - the term for that we want to encode the pi-properness
     * @param arities - the arities that have been demanded so far, will not be changed
     * @param afs - the set of (f/i) that are definitely regarded, will not be changed
     * @param state - the arities and the proper-arities will be updated
     * @param dpState - if not null, then t must be of the form A(t1,t2) where A is a head symbol.
     *         then the result of encodeProper(t2) is stored in second-Part of the dpState.
     */
    private void encodeProper(
            Triple<Formula<Property>, TRSTerm, TRSTerm> result,
            TRSTerm t,
            Map<FunctionSymbol, Integer> arities,
            Set<Pair<FunctionSymbol, Integer>> afs,
            State state,
            DpState dpState) {

        if (t.isVariable()) {
            result.x = this.tt;
            result.y = t;
            return;
        } else {
            Triple<TRSTerm, FunctionSymbol[], TRSTerm[]> partition = QApplicativeUsableRules.partition(t);
            TRSTerm root = partition.x;

            if (root.isVariable()) {
                if (dpState != null) {
                    TRSTerm secondArg = ((TRSFunctionApplication)t).getArgument(1);
                    this.encodeProper(result, secondArg, arities, afs, state, null);
                    dpState.secondALeft = result.y;
                    dpState.secondPhi = result.x;
                    dpState.secondArities = state.arities;
                    state.arities = new HashMap<FunctionSymbol, Set<Integer>>(0);
                }
                this.getNonProperResultWithGivenCap(result, state, null);
                return;
            } else {
                if (dpState != null) {
                    TRSTerm secondArg = ((TRSFunctionApplication)t).getArgument(1);
                    this.encodeProper(result, secondArg, arities, afs, state, null);
                    dpState.secondALeft = result.y;
                    dpState.secondPhi = result.x;
                    dpState.secondArities = QApplicativeUsableRules.copyArityMap(state.arities);
                }

                boolean storedArity;
                // the list of conjuncts will be phi
                List<Formula<Property>> phi;
                TRSTerm[] args = partition.z;
                final int arity = args.length;

                // here t is partitioned into f '1 t_1 '2 ... 'n t_n
                FunctionSymbol f = ((TRSFunctionApplication) root).getRootSymbol();
                Integer formerArity = arities.put(f, arity);
                if (formerArity == null) {
                    // we have not seen f before, so store arity and demand it.
                    storedArity = true;
                    phi = new ArrayList<Formula<Property>>(arity+1);
                    phi.add(this.getPropForArity(state, f, arity));
                } else {
                    if (formerArity.intValue() == arity) {
                        // we don't have to demand arity as it is demanded already above
                        storedArity = false;
                        phi = new ArrayList<Formula<Property>>(arity);
                    } else {
                        // conflict of arities (cannot happen if dpstate != null)
                        if (Globals.useAssertions) {
                            assert(dpState == null);
                        }
                        arities.put(f, formerArity); // undo to be non-destructive
                        this.getNonProperResultWithGivenCap(result, state, null);
                        return;
                    }
                }
                // we have no conflict up to now
                // so let us look at the arguments
                FunctionSymbol ff = this.getFunctionalSymbol(f, partition.y);
                ArrayList<TRSTerm> resArgs = new ArrayList<TRSTerm>(arity);
                for (int i = 0; i<arity; i++) {
                    // can we use the computation we have used before?
                    if (dpState == null || i != arity-1) {
                        // we have to compute
                        Pair<FunctionSymbol, Integer> ff_i = new Pair<FunctionSymbol, Integer>(ff, i);
                        boolean storedAF = afs.add(ff_i);
                        this.encodeProper(result, args[i], arities, afs, state, null);
                        Formula<Property> phii = result.x;
                        resArgs.add(result.y);
                        if (storedAF) {
                            afs.remove(ff_i);
                            phii = this.ffactory.buildImplication(this.getPropForAF(ff, i), phii);
                        }
                        phi.add(phii);
                    } else {
                        // we can use previous result
                        if (Globals.useAssertions) {
                            assert(i == arity-1);
                        }
                        resArgs.add(dpState.secondALeft);
                        phi.add(this.ffactory.buildImplication(this.getPropForAF(ff, i),dpState.secondPhi));
                    }
                }

                if (storedArity) {
                    arities.remove(f);
                }
                result.x = this.ffactory.buildAnd(phi);
                result.y = TRSTerm.createFunctionApplication(ff, ImmutableCreator.create(resArgs));
            }
        }
    }


    /**
     * Encodes that a term t is pi-proper and returns additionally the
     * a-transformed term and the term cap^S_Q,R(t) where fresh vars are introduced by SECOND STANDARD
     * Those parts that are not proper (and hence cannot be
     * transformed by a-transformation) are replaced by the dummy-term.
     * @param origRule - the rule in which t occurs as a subterm of a rhs, for a DP this should be null
     * @param nextNr - the next fresh variable nr for cap
     * @param result - put the formula and the a-transformed term here.
     * @param t - the term for that we want to encode the pi-properness and usable rules, vars have to be from THIRD STANDARD
     * @param arities - the arities that have been demanded so far, must not be changed
     * @param afs - the set of (f/i) that are definitely regarded, must not be changed
     * @param state - the usable rules, the arities and the proper-arities will be updated
     * @return the nextNr that can be used afterwards
     */
    private int encodeProperAndUsable(
            Triple<Formula<Property>, TRSTerm, TRSTerm> result,
            Rule origNonDPRule,
            TRSTerm t,
            int nextNr,
            TRSTerm[] S,
            Map<FunctionSymbol, Integer> arities,
            Set<Pair<FunctionSymbol, Integer>> afs,
            State state,
            DpState dpState) {
        if (t.isVariable()) {
            result.x = this.tt;
            result.y = t;
            result.z = this.innermost ? t : TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX+(nextNr++));
            return nextNr;
        } else {
            Triple<TRSTerm, FunctionSymbol[], TRSTerm[]> partition = QApplicativeUsableRules.partition(t);
            TRSTerm root = partition.x;

            if (root.isVariable()) {
                if (dpState != null) {
                    // it still may be possible that the second argument is pi-proper,
                    // so let us do the corresponding computation and store it as second result
                    TRSTerm secondArg = ((TRSFunctionApplication)t).getArgument(1);
                    state.arities = dpState.secondArities;
                    nextNr = this.encodeProperAndUsable(result, origNonDPRule, secondArg, nextNr, S, arities, afs, state, null);
                    dpState.secondARight = result.y;
                    dpState.secondPhi = this.ffactory.buildAnd(dpState.secondPhi, result.x);
                    dpState.secondArities = state.arities;
                    dpState.secondUsableRules = state.usableRules;
                    state.arities = new HashMap<FunctionSymbol, Set<Integer>>(0);
                    state.usableRules = QApplicativeUsableRules.emptyRules;
                    state.phi = this.ff;
                }
                return this.getNonProperResult(result, state, S, t, nextNr);
            } else {
                Formula<Property> secondPhi;
                TRSTerm secondCapped;
                if (dpState != null) {
                    // encodeProperAndUsable for second argument on fresh state
                    // where arities are fresh
                    Map<FunctionSymbol, Set<Integer>> oldArities = state.arities;
                    state.arities = new HashMap<FunctionSymbol, Set<Integer>>();
                    TRSTerm secondArg = ((TRSFunctionApplication)t).getArgument(1);
                    nextNr = this.encodeProperAndUsable(result, origNonDPRule, secondArg, nextNr, S, arities, afs, state, null);
                    // then afterwards merge the results into main state
                    dpState.secondARight = result.y;
                    secondCapped = result.z;
                    secondPhi = result.x;
                    dpState.secondPhi = this.ffactory.buildAnd(dpState.secondPhi, secondPhi);
                    state.mergeArities(dpState.secondArities);
                    state.mergeArities(oldArities);
                    state.arities = oldArities;
                    dpState.secondUsableRules = state.usableRules;
                    state.usableRules = new HashSet<Rule>(state.usableRules);
                } else {
                    secondPhi = null;
                    secondCapped = null;
                }

                boolean storedArity;
                // the list of conjuncts will be phi
                List<Formula<Property>> phi;
                TRSTerm[] args = partition.z;
                final int arity = args.length;

                // here t is partitioned into f '1 t_1 '2 ... 'n t_n
                FunctionSymbol f = ((TRSFunctionApplication) root).getRootSymbol();
                Integer formerArity = arities.put(f, arity);
                if (formerArity == null) {
                    // we have not seen f before, so store arity and demand it.
                    storedArity = true;
                    phi = new ArrayList<Formula<Property>>(arity+3);  // assume that 2 rules are usable (1 needed for arity)
                    phi.add(this.getPropForArity(state, f, arity));
                } else {
                    if (formerArity.intValue() == arity) {
                        // we don't have to demand arity as it is demanded already above
                        storedArity = false;
                        phi = new ArrayList<Formula<Property>>(arity+2); // assume that 2 rules are usable
                    } else {
                        // conflict of arities (cannot occur if dpState is non-null)
                        arities.put(f, formerArity); // undo to be non-destructive
                        return this.getNonProperResult(result, state, S, t, nextNr);
                    }
                }

                // we have no conflict up to now
                // so let us look at the arguments
                FunctionSymbol ff = this.getFunctionalSymbol(f, partition.y);
                ArrayList<TRSTerm> resArgs = new ArrayList<TRSTerm>(arity);
                TRSTerm[] capArgs = new TRSTerm[arity];
                for (int i = 0; i<arity; i++) {
                    if (dpState == null || i != arity-1) {
                        Pair<FunctionSymbol, Integer> ff_i = new Pair<FunctionSymbol, Integer>(ff, i);
                        boolean storedAF = afs.add(ff_i);
                        nextNr = this.encodeProperAndUsable(result, origNonDPRule, args[i], nextNr, S, arities, afs, state, null);
                        Formula<Property> phii = result.x;
                        resArgs.add(result.y);
                        capArgs[i] = result.z;
                        if (storedAF) {
                            afs.remove(ff_i);
                            phii = this.ffactory.buildImplication(this.getPropForAF(ff, i), phii);
                        }
                        phi.add(phii);
                    } else {
                        if (Globals.useAssertions) {
                            assert(i == arity-1);
                        }
                        phi.add(this.ffactory.buildImplication(this.getPropForAF(ff, i), secondPhi));
                        resArgs.add(dpState.secondARight);
                        capArgs[i] = secondCapped;
                    }
                }

                if (storedArity) {
                    arities.remove(f);
                }

                // cap computation on top-level
                Triple<TRSTerm, Set<Rule>, Integer> capResult = this.computeCap(S, root, partition.y, capArgs, nextNr, true);
                nextNr = capResult.z;
                Set<Rule> usableRules = capResult.y;

                if (usableRules == null) { // we had a conflict, so usable rules are not proper
                    this.getNonProperResultWithGivenCap(result, state, capResult.x);
                    return nextNr;
                } else {
                    // we have to enforce that all these rules are usable
                    // (of course not for the original rule)

                    if (!usableRules.isEmpty()) {
                        if (QApplicativeUsableRules.specialize) {
                            ValueCache<Property> usedFlags = new SimpleValueCache<Property>(this.ffactory);

                            List<Formula<Property>> usableFlags = new ArrayList<Formula<Property>>(usableRules.size());

                            for (Rule rule : usableRules) {
                                if (!rule.equals(origNonDPRule)) {
                                    state.usableRules.add(rule);
                                    TheoryAtom<Property> usedFlag = this.stateMap.get(rule).usedFlag;
                                    usedFlags.assertValue(usedFlag, true);
                                    usableFlags.add(usedFlag);
                                }
                            }

                            if (!usableFlags.isEmpty()) {
                                // specialize previous conditions
                                ListIterator<Formula<Property>> phiIt = phi.listIterator();
                                while (phiIt.hasNext()) {
                                    phiIt.set(phiIt.next().evaluate(usedFlags));
                                }
                                // and add usable flags
                                phi.addAll(usableFlags);
                            }

                        } else {
                            // don't specialize formula
                            for (Rule rule : usableRules) {
                                if (!rule.equals(origNonDPRule)) {
                                    state.usableRules.add(rule);
                                    phi.add(this.stateMap.get(rule).usedFlag);
                                }
                            }
                        }
                    }

                    result.x = this.ffactory.buildAnd(phi);
                    result.y = TRSTerm.createFunctionApplication(ff, ImmutableCreator.create(resArgs));
                    result.z = capResult.x;

                    return nextNr;
                }
            }
        }
    }

    /**
     * given a term t and counter for fresh names this method stores
     * the term cap^S(t) in the pair and updates the fresh name counter
     * @param S
     * @param t_nextNr
     */
    private void computeCap(TRSTerm[] S, Pair<TRSTerm, Integer> t_nextNr) {
        TRSTerm t = t_nextNr.x;
        if (t.isVariable()) {
            if (!this.innermost) {
                int nextNr = t_nextNr.y;
                t_nextNr.x = TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX+(nextNr++));
                t_nextNr.y = nextNr;
            }
        } else {
            Triple<TRSTerm,FunctionSymbol[],TRSTerm[]> partition = QApplicativeUsableRules.partition(t);
            TRSTerm[] args = partition.z;
            int n = args.length;
            for (int i = 0; i<n; i++) {
                t_nextNr.x = args[i];
                this.computeCap(S, t_nextNr);
                args[i] = t_nextNr.x;
            }
            Triple<TRSTerm, Set<Rule>, Integer> capResult = this.computeCap(S, partition.x, partition.y, args, t_nextNr.y, false);
            t_nextNr.x = capResult.x;
            t_nextNr.y = capResult.z;
        }
    }

    /**
     * computes cap^S(xf'cap(t1)'..'cap(tn)) and determines the set of usable rules on top-level
     * @param S
     * @param xf either a variable or a constant
     * @param apSyms the application symbols '
     * @param capArgs the list cap(t1)..cap(tn)
     * @param nextNr the next free number to obtain fresh vars
     * @param wantUsable indicate whether we are interested on usable rules, or if false only on the capped term
     * @return the capped term;
     *          the set of usable rules (null, if wantUsable is false, of if usable-rules are inproper together with the term xf'...'cap(tn);
     *          the next free nr for creating fresh vars
     */
    private Triple<TRSTerm, Set<Rule>, Integer> computeCap(TRSTerm[] S, TRSTerm xf, FunctionSymbol[] apSyms, TRSTerm[] capArgs, int nextNr, boolean wantUsable) {
        final int n = apSyms.length;
        FunctionSymbol f;
        Triple<TRSTerm, Set<Rule>, Integer> result = new Triple<TRSTerm, Set<Rule>, Integer>(null, wantUsable ? new HashSet<Rule>() : null, null);

        // first compute cap(x) or cap(f)
        if (xf.isVariable()) {
            wantUsable = false;
            f = null;
        } else {
            TRSFunctionApplication ft = (TRSFunctionApplication) xf;
            f = ft.getRootSymbol();
            Set<Rule> fRules = this.R.get(f);
            if (fRules != null) {
                boolean wantNow = wantUsable && n == 0;
                boolean nullifyF = false;
                for (Rule rule : fRules) {
                    if (rule.getRootSymbol().equals(f)) {
                        xf = TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX+(nextNr++));
                        nullifyF = true;
                        if (wantNow) {
                            result.y.add(rule);
                        } else {
                            // store that even if we to be proper then usable rules are inproper
                            // as we have an arity conflict
                            wantUsable = false;
                            break;
                        }
                    }
                }
                if (nullifyF) {
                    f = null;
                }
            }
        }

        // we have the invariant that
        // xf = cap(x/f ' ... ' t_{i-1})
        iLoop: for (int i=0; i<n; i++) {
            TRSFunctionApplication capApCap = TRSTerm.createFunctionApplication(apSyms[i], new TRSTerm[]{xf, capArgs[i]});

            if (f != null) {
                // we have a term f'..'cap(t_i)

                // first check x'..'.-Rules
                Set<Rule> xRules = this.R.get(null);
                if (xRules != null) {
                    for (Rule rule : xRules) {
                        if (this.checkRuleApplication(rule, capApCap, S)) {
                            xf = TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX+(nextNr++));
                            f = null;
                            // store that even if we want to be proper then the usable rules are inproper
                            // as we have a usable rule x'..'..
                            wantUsable = false;
                            continue iLoop;
                        }
                    }
                }

                // then check f'..'.-Rules
                Set<Rule> fRules = this.R.get(f);
                if (fRules != null) {
                    boolean wantNow = wantUsable && i == n-1;
                    boolean replaceByFresh = false;
                    for (Rule rule : fRules) {
                        if (this.checkRuleApplication(rule, capApCap, S)) {
                            replaceByFresh = true;
                            f = null;
                            if (wantNow) {
                                result.y.add(rule);
                            } else {
                                // store that even if we want to be proper then the usable rules are inproper
                                // as we have an arity conflict
                                wantUsable = false;
                                continue iLoop;
                            }
                        }
                    }
                    if (replaceByFresh) {
                        xf = TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX+(nextNr++));
                        continue iLoop;
                    }
                }
            } else {
                // we already have a term of the form x'..'..
                // thus possibly all rules are applicable
                for (Set<Rule> rules : this.R.values()) {
                    for (Rule rule : rules) {
                        if (this.checkRuleApplication(rule, capApCap, S)) {
                            xf = TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX+(nextNr++));
                            if (Globals.useAssertions) {
                                assert(!wantUsable); // we should have turned of wantUsable already
                            }
                            continue iLoop;
                        }
                    }
                }
            }

            // okay, we don't have to replace capApCap by a fresh variable,
            // so Cap(cap(x'..'cap(t_i-1) ' cap(t_i)) = capApCap and we can continue with this term
            // for the next iteration
            xf = capApCap;
        }

        if (!wantUsable) {
            result.y = null;
        }

        result.x = xf;
        result.z = nextNr;
        return result;
    }

    /**
     * checks whether the rule can possibly be applied on t sigma where
     * S sigma is normal form
     * @param rule a rule
     * @param t a term which does not possess vars in FIRST STANDARD
     * @param S
     */
    private boolean checkRuleApplication(Rule rule, TRSTerm t, TRSTerm[] S) {
        return rule.getLhsInStandardRepresentation().unifies(t);
                // TODO integrate normal checks here!!
    }


    private void getNonProperResultWithGivenCap(Triple<Formula<Property>, TRSTerm, TRSTerm> result, State state, TRSTerm capped) {
        result.x = this.ff;
        result.y = QApplicativeUsableRules.dummy;
        state.properArities = null;
        result.z = capped;
    }

    private int getNonProperResult(Triple<Formula<Property>, TRSTerm, TRSTerm> result, State state, TRSTerm[] S, TRSTerm capThis, int nextNr) {
        Pair<TRSTerm, Integer> t_nextNr = new Pair<TRSTerm, Integer>(capThis, nextNr);
        this.computeCap(S, t_nextNr);
        this.getNonProperResultWithGivenCap(result, state, t_nextNr.x);
        return t_nextNr.y;
    }

    /**
     * returns the function symbol for f_apSyms
     * @param f
     * @param apSyms
     * @return
     */
    private FunctionSymbol getFunctionalSymbol(FunctionSymbol f, FunctionSymbol[] apSyms) {
        final int n = apSyms.length;
        List<FunctionSymbol> fs = new ArrayList<FunctionSymbol>(n+1);
        fs.add(f);
        for (int i=0; i<n; i++) {
            fs.add(apSyms[i]);
        }
        FunctionSymbol ff = this.applToFuncSignature.get(fs);
        if (ff == null) {
            final String fName = f.getName();
            String wishName = fName;
            int i = 0;
            while (ff == null) {
                ff = FunctionSymbol.create(wishName, n);
                if (!this.funcSignature.add(ff)) {
                    ff = null;
                    i++;
                    wishName = fName+i;
                }
            }
            this.applToFuncSignature.put(fs, ff);
        }
        return ff;
    }

    /**
     * encode ar(f) = n
     * @param f a constant of the applicative signature
     * @param n
     * @return
     */
    private Formula<Property> getPropForArity(State state, FunctionSymbol f, int n) {
        // check whether we are not proper any more
        Map<FunctionSymbol, Integer> propArs = state.properArities;
        if (propArs != null) {
            Integer oldAr = propArs.put(f, n);
            if (oldAr != null && oldAr.intValue() != n) {
                // clash
                state.properArities = null;
            }
        }

        // store that we have seen a new arity
        Set<Integer> ars = state.arities.get(f);
        if (ars == null) {
            ars = new TreeSet<Integer>();
            state.arities.put(f, ars);
        }
        ars.add(n);

        return this.ffactory.buildTheoryAtom(new ArityProp(f,n));
    }

    /**
     * encode pi(ff) contains n
     * @param ff a function symbol of the functional signature
     * @param n
     * @return
     */
    private Formula<Property> getPropForAF(FunctionSymbol ff, int n) {
        return this.ffactory.buildTheoryAtom(new AfsProp(ff,n));
    }


    /**
     * docu-guess (fuhs):
     * Extension of a state for rules from P:
     * Here, it makes sense to consider the arities, usable rules, etc.
     * also for the argument filtering which filters APP (i.e., the sharped
     * version of the app-symbol) to its <b>second</b> argument. This way,
     * sometimes arity conflicts can be avoided, but not filtering APP is
     * usually preferred since it corresponds to a more general case (i.e.,
     * the solver applied on the A-transformed problem can then choose
     * whether to simulate this filtering or not).
     */
    private static class DpState extends State {

        public DpState(Rule rule) {
            super(rule,null);
        }

        private TRSTerm                              secondALeft;
        private TRSTerm                              secondARight;
        private Map<FunctionSymbol, Set<Integer>> secondArities;
        private Set<Rule>                         secondUsableRules;
        private Formula<Property>                 secondPhi;

        /**
         * compute whether we can apply get a second result for the
         * given set of head syms. If this is possible a boolean value
         * is returned which determines what the second result is.
         * @param headSyms
         * @return
         */
        public YNM getSecond(Set<FunctionSymbol> headSyms) {
            boolean leftDC = this.rule.getRootSymbol().getArity() == 0;
            boolean leftSecond = headSyms.contains(this.rule.getRootSymbol());
            boolean rightDC,rightSecond;
            TRSTerm right = this.rule.getRight();
            if (right.isVariable()) {
                rightDC = true;
                rightSecond = true;
            } else {
                FunctionSymbol f = ((TRSFunctionApplication)right).getRootSymbol();
                rightDC = f.getArity() == 0;
                rightSecond = headSyms.contains(f);
            }
            if (leftDC) {
                return YNM.fromBool(rightSecond);
            } else if (rightDC) {
                return YNM.fromBool(leftSecond);
            } else if (leftSecond && rightSecond) {
                return YNM.YES;
            } else if (leftSecond || rightSecond) {
                // if only one is true then we disallow usage of second, as we did not separate the second parts!
                return YNM.MAYBE;
            } else {
                return YNM.NO;
            }
        }

        public void mergeSecondArities(Map<FunctionSymbol, Set<Integer>> arities, boolean second) {
            if (second) {
                State.mergeArities(arities, this.secondArities);
            } else {
                State.mergeArities(arities, this.arities);
            }
        }

        public Set<Rule> getSecondUsable(boolean second) {
            if (second) {
                return this.secondUsableRules;
            } else {
                return this.usableRules;
            }
        }

        public Formula<Property> getSecondPhi(boolean second) {
            if (second) {
                return this.secondPhi;
            } else {
                return this.phi;
            }
        }

        public Pair<TRSTerm, TRSTerm> getSecondARule(boolean second) {
            if (second) {
                return new Pair<TRSTerm, TRSTerm>(this.secondALeft, this.secondARight);
            } else {
                return new Pair<TRSTerm, TRSTerm>(this.aRule.getLeft(), this.aRule.getRight());
            }
        }

        @Override
        public String toString() {
            String s = "Second result:\n";
            s += "Second a rule:\n  ";
            s += this.secondALeft + " -> " + this.secondARight+"\n";
            s += "We have the following second arities\n";
            for (Map.Entry<FunctionSymbol, Set<Integer>> f_ar : this.secondArities.entrySet()) {
                s += "  "+f_ar.getKey() + " / {";
                boolean first = true;
                for (Integer n : f_ar.getValue()) {
                    if (first) {
                        first = false;
                    } else {
                        s += ",";
                    }
                    s += n;
                }
                s += "}\n";
            }
            if (this.secondUsableRules.isEmpty()) {
                s += "There are no second usable rules\n";
            } else {
                s += "We have the following set of second usable rules\n";
                for (Rule usable : this.secondUsableRules) {
                    s += "  "+usable+"\n";
                }
            }
            s += "The second formula is\n  " + this.secondPhi+"\n\n";
            return super.toString() + s;
        }
    }

    private static class State {
        final Rule rule;
        final TheoryAtom<Property> usedFlag;
        Map<FunctionSymbol, Integer> properArities; // non-conflicting arities
                                                             // if confl. arities or x ' t_1 ' ... ' t_n is occur. in rule then null

        Map<FunctionSymbol, Set<Integer>> arities;  // all used arities, e.g. if rule = f'(g'x)'(f'y) -> 0
                                                             // we get map f->{1,2}, g->{0}, 0 -> {0}

        Set<Rule> usableRules;                      // the set of rules that are usable for this rule under
                                                             // the condition that this rule is pi-proper!
                                                             // e.g. for rule f'x'y -> g'(x'y)'(h'x'y)
                                                             // we will get the h-rules as usable, but not necessarily the
                                                             // usable rules for the term x'y as the proper condition
                                                             // will guarantee that g's first argument is dropped by pi

        Formula<Property> phi;                      // the usable-rules formula for the rule

        GeneralizedRule aRule;                                 // the a-transformed rule of this term.
                                                             // if phi is false, dummy -> dummy formula is used,
                                                             // otherwise unproper parts are replaced by dummy,
                                                             // e.g. for rule f'x'y -> g'(x'y)'(h'x'y) we will get f(x,y) -> g(dummy,h(x,y))

        public State(Rule rule, TheoryAtom<Property> usedFlag) {
            this.rule = rule;
            this.usableRules = new HashSet<Rule>();
            this.usedFlag = usedFlag;
        }

        /**
         * tries to merge the required arities of this state into the
         * given arity-map.
         * @param arity
         * @return true, iff the merging was successful
         */
        public boolean mergeProperArity(Map<FunctionSymbol, Integer> arity) {
            if (this.properArities == null) {
                return false; // we on our own are inproper
            } else {
                for (Map.Entry<FunctionSymbol, Integer> f_ar : this.properArities.entrySet()) {
                    Integer myarity = f_ar.getValue();
                    Integer ar = arity.put(f_ar.getKey(), myarity);
                    if (ar != null && ar.intValue() != myarity) {
                        return false; // conflict
                    }
                }
                return true;
            }
        }

        /**
         * merges all arities of this state into the
         * given arity-map.
         * @param arities
         */
        public void mergeArities(Map<FunctionSymbol, Set<Integer>> arities) {
            State.mergeArities(arities, this.arities);
        }

        /**
         * merges all arities of this "unchanged" into the map "arities"
         * @param arities - will be changed
         * @param unchanged - will not be changed
         */
        protected static void mergeArities(Map<FunctionSymbol, Set<Integer>> arities, Map<FunctionSymbol, Set<Integer>> unchanged) {
            for (Map.Entry<FunctionSymbol, Set<Integer>> f_arities : unchanged.entrySet()) {
                Set<Integer> uncArities = f_arities.getValue();
                FunctionSymbol f = f_arities.getKey();
                Set<Integer> givenArities = arities.get(f);
                if (givenArities == null) {
                    arities.put(f, new TreeSet<Integer>(uncArities));
                } else {
                    givenArities.addAll(uncArities);
                }
            }
        }





        @Override
        public String toString() {
            String s = "Encoded rule\n  " + this.rule + "\ninto a-rule\n  " + this.aRule + "\n";
            if (this.properArities == null) {
                s += "The rule is not proper and we have the following arities\n";
                for (Map.Entry<FunctionSymbol, Set<Integer>> f_ar : this.arities.entrySet()) {
                    s += "  "+f_ar.getKey() + " / {";
                    boolean first = true;
                    for (Integer n : f_ar.getValue()) {
                        if (first) {
                            first = false;
                        } else {
                            s += ",";
                        }
                        s += n;
                    }
                    s += "}\n";
                }
            } else {
                s += "The rule is proper with the following arities\n";
                for (Map.Entry<FunctionSymbol, Integer> f_ar : this.properArities.entrySet()) {
                    s += "  "+f_ar.getKey()+ " / " + f_ar.getValue()+"\n";
                }
            }
            if (this.usableRules.isEmpty()) {
                s += "There are no usable rules\n";
            } else {
                s += "We have the following set of usable rules\n";
                for (Rule usable : this.usableRules) {
                    s += "  "+usable+"\n";
                }
            }
            s += "The formula is\n  " + this.phi+"\n";

            return s;
        }
    }

    private static interface Property {};


    private static class ArityProp implements Property {
        public final FunctionSymbol f;
        public final int arity;

        public ArityProp(FunctionSymbol f, int arity) {
            this.arity = arity;
            this.f = f;
        }

        @Override
        public String toString() {
            return "ar("+this.f+")="+this.arity;
        }
        @Override
        public int hashCode() {
            return this.f.hashCode()+101*this.arity;
        }
        @Override
        public boolean equals(Object o) {
            if (!(o instanceof ArityProp)) {
                return false;
            }
            ArityProp other = (ArityProp)o;
            if (this.arity != other.arity) {
                return false;
            }
            if (this.f != other.f) {
                if (this.f == null) {
                    return other.f == null;
                }
                if (!this.f.equals(other.f)) {
                    return false;
                }
            }
            return true;
        }
    }

    public static class AfsProp implements Property {
        public final FunctionSymbol f;
        public final int i;

        public AfsProp(FunctionSymbol f, int i) {
            this.i = i;
            this.f = f;
        }

        @Override
        public String toString() {
            return this.i+"eRP("+this.f+")";
        }
        @Override
        public int hashCode() {
            return this.f.hashCode()+101*this.i;
        }
        @Override
        public boolean equals(Object o) {
            if (!(o instanceof AfsProp)) {
                return false;
            }
            AfsProp other = (AfsProp)o;
            if (this.i != other.i) {
                return false;
            }
            if (this.f != other.f) {
                if (this.f == null) {
                    return other.f == null;
                }
                if (!this.f.equals(other.f)) {
                    return false;
                }
            }
            return true;
        }
    }

    private static class UsableProp implements Property {
        public final Rule rule;
        public final int id;

        public UsableProp(Rule rule, int id) {
            this.rule = rule;
            this.id = id;
            if (Globals.DEBUG_THIEMANN) {
                System.out.println("us("+id+") for rule "+rule);
            }
        }

        @Override
        public String toString() {
            return "us("+this.id+")";
        }
    }


}
