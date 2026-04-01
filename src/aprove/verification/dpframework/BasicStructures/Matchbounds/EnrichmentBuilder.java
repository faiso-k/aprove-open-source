package aprove.verification.dpframework.BasicStructures.Matchbounds;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.TRSBounds.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.TRSBoundsHelper.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.TreeAutomaton.*;
import immutables.*;

public abstract class EnrichmentBuilder {
    protected final Bound enrichment;
    protected Set<Rule> origTRS;

    protected Set<FunctionSymbol> annotLhsSignature;
    protected Set<Rule> enrichedTRS;

    protected BijectiveFSToAFSMapper fSMapper;
    protected FunctionSymbolGenerator funcSymbGen;

    protected TreeAutomaton<FunctionSymbol, Integer> curA = null;

    public EnrichmentBuilder(Bound enrichment, Set<Rule> origTRS) {
        this.enrichment = enrichment;
        this.origTRS = origTRS;
        this.annotLhsSignature = new LinkedHashSet<FunctionSymbol>();

        this.enrichedTRS = new LinkedHashSet<Rule>();

        this.fSMapper = new BijectiveFSToAFSMapper();
        this.funcSymbGen = new FunctionSymbolGenerator(CollectionUtils.getFunctionSymbols(origTRS));
    }

    public void SetTAForCurCompConflicts(TreeAutomaton<FunctionSymbol, Integer> curA) {
        this.curA = curA;
        this.updateEnrichedTRS();
    }

    public Set<FunctionSymbol> getLhsSignature() {
        return this.annotLhsSignature;
    }

    public void setLhsSignature(Set<FunctionSymbol> lhsSignature) {
        this.annotLhsSignature = new LinkedHashSet<FunctionSymbol>(lhsSignature);
        this.updateEnrichedTRS();
    }

    public Set<Rule> getTRS() {
        return this.enrichedTRS;
    }

    public Set<Rule> getOrigTRS() {
        return this.origTRS;
    }

    public FunctionSymbolGenerator getFuncSymbGen() {
        return this.funcSymbGen;
    }

    public void addToSignature(Set<FunctionSymbol> functionSymbols) {
        for (FunctionSymbol f : functionSymbols) {
                this.annotLhsSignature.add(f);
        }

        this.updateEnrichedTRS();
    }

    protected abstract void updateEnrichedTRS();

    protected Set<Position> getTopPositions(Rule r) {
        Set<Position> top = new LinkedHashSet<Position>();
        top.add(Position.create());
        return top;
    }

    protected Set<Position> getRoofPositions(Rule r) {
        TRSFunctionApplication lhs = r.getLeft();
        TRSTerm rhs = r.getRight();
        // Compute roof(lhs, rhs)
        Set<TRSVariable> rhsVariables = rhs.getVariables();
        Set<Position> positions = lhs.getPositions();
        Set<Position> roof = new LinkedHashSet<Position>();
        for (Position pos : positions) {
            //check if pos is a roof position w.r.t. the set rhsVariables
            TRSTerm subTerm = lhs.getSubterm(pos);
            Set<TRSVariable> subTermVariables = subTerm.getVariables();
            if ((!subTerm.isVariable()) && subTermVariables.containsAll(rhsVariables)) {
                roof.add(pos);
            }
        }

        return roof;
    }

    protected Set<Position> getMatchPositions(Rule r) {
        TRSFunctionApplication lhs = r.getLeft();
        // Compute match(lhs, rhs)
        Set<Position> positions = lhs.getPositions();
        Map<TRSVariable, List<Position>> variablePositions = lhs.getVariablePositions();
        Set<Position> match = positions;
        for (Map.Entry<TRSVariable, List<Position>> entry : variablePositions.entrySet()) {
            match.removeAll(entry.getValue());
        }

        return match;
    }

    /*
     * creates e(l-->r) for e: FunctionApplication X Term --> Set<Position>, where the set of positions may only contain positions i where l(i) is a FunctionSymbol.
     * updates romR.
     */
    protected void createER(TRSFunctionApplication origLhs, TRSTerm origRhs, Set<Position> e) {

        if (Globals.useAssertions) {
            assert (!e.isEmpty());
            for (Position p : e) {
                assert (origLhs.getSubterm(p) instanceof TRSFunctionApplication);
            }
        }

        boolean buildRule = false;
        Set<FunctionSymbol> signatureToBeUsed = new LinkedHashSet<FunctionSymbol>(this.annotLhsSignature);
        if (this.curA == null) {
            buildRule = true;
        } else {
            TreeAutomaton<FunctionSymbol, Integer> heurA;
            Set<Transition<FunctionSymbol, Integer>> heurTranss = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();
            for (Transition<FunctionSymbol, Integer> curATrans : this.curA.getTransitions()) {
                Transition<FunctionSymbol, Integer> heurATrans = Transition.create(this.base(curATrans.getLhsFunctionSymbol()),
                    curATrans.getLhsStateParameters(), curATrans.getRhsState());
                heurTranss.add(heurATrans);
            }
            heurA = TreeAutomaton.create(this.curA.getFinalStates(), heurTranss, this.curA.getEpsTransitions());
            Set<Integer> allStates = heurA.getAllStates();
            for (Integer target : heurA.getAllStates()) {
                Set<StateSubstitution<Integer>> stateSubss = TRSBoundsTA.createStateSubstitutions(heurA, origLhs, target, allStates);
                if (!stateSubss.isEmpty()) {
                    buildRule = true;
                    break;
                }
            }
        }

        if (buildRule) {
            Set<TRSTerm> newLhss = this.buildTermsWithSameBase(origLhs, this.annotLhsSignature);
            for (TRSTerm l : newLhss) {
                TRSFunctionApplication lhs = (TRSFunctionApplication) l;

                int minHeightInLhs = Integer.MAX_VALUE;
                for (Position p : e) {
                    TRSFunctionApplication fA = (TRSFunctionApplication) l.getSubterm(p);
                    int height = this.height(fA.getRootSymbol());

                    if (height < minHeightInLhs) {
                        minHeightInLhs = height;
                    }
                }

                int rhsHeight = minHeightInLhs + 1;

                TRSTerm rhs = this.lift(origRhs, rhsHeight);
                Rule newRule = Rule.create(lhs, rhs);
                this.enrichedTRS.add(newRule);
            }
        }
    }

    /*
     * creates e-DP(l-->r).
     * updates romR.
     */
    protected void createEDPR(TRSFunctionApplication origLhs, TRSTerm origRhs, Set<Position> e) {

        if (Globals.useAssertions) {
            assert (!e.isEmpty());
            for (Position p : e) {
                assert (origLhs.getSubterm(p) instanceof TRSFunctionApplication);
            }
        }

        Set<TRSTerm> newLhss = this.buildTermsWithSameBase(origLhs, this.annotLhsSignature);
        for (TRSTerm l : newLhss) {
            TRSFunctionApplication lhs = (TRSFunctionApplication) l;

            int minHeightInLhs = this.height(lhs.getRootSymbol());
            boolean minIsAtRoot = true;
            for (Position p : e) {

                TRSFunctionApplication fA = (TRSFunctionApplication) l.getSubterm(p);
                int height = this.height(fA.getRootSymbol());

                if (height < minHeightInLhs) {
                    minHeightInLhs = height;
                    minIsAtRoot = false;
                }

            }

            int rhsHeight;
            if (minIsAtRoot) {
                rhsHeight = minHeightInLhs;
            } else {
                rhsHeight = minHeightInLhs + 1;
            }

            TRSTerm rhs = this.lift(origRhs, rhsHeight);
            Rule newRule = Rule.create(lhs, rhs);
            this.enrichedTRS.add(newRule);
        }
    }

    protected void createERTR(TRSFunctionApplication origLhs, TRSTerm origRhs, Set<Position> e) {

        if (Globals.useAssertions) {
            assert (!e.isEmpty());
            for (Position p : e) {
                assert (origLhs.getSubterm(p) instanceof TRSFunctionApplication);
            }
        }

        boolean isSizeDecrOrPresRule;
        if (this.sizeWRTFS(origLhs) >= this.sizeWRTFS(origRhs)) {
            isSizeDecrOrPresRule = true;
        } else {
            isSizeDecrOrPresRule = false;
        }

        Set<TRSTerm> newLhss = this.buildTermsWithSameBase(origLhs, this.annotLhsSignature);

        for (TRSTerm l : newLhss) {
            TRSFunctionApplication lhs = (TRSFunctionApplication) l;

            int heightOfRoot = this.height(lhs.getRootSymbol());
            int rhsHeight;
            if (isSizeDecrOrPresRule && l.equals(this.lift(origLhs, heightOfRoot))) {
                rhsHeight = heightOfRoot;
            } else {
                int minHeightInLhs = heightOfRoot;
                for (Position p : e) {
                    TRSFunctionApplication fA = (TRSFunctionApplication) l.getSubterm(p);
                    int height = this.height(fA.getRootSymbol());

                    if (height < minHeightInLhs) {
                        minHeightInLhs = height;
                    }

                }
                rhsHeight = minHeightInLhs;
            }


            TRSTerm rhs = this.lift(origRhs, rhsHeight);
            Rule newRule = Rule.create(lhs, rhs);
            this.enrichedTRS.add(newRule);
        }
    }

    /*
     * returns the function symbol representing f_i for parameters f and i
     */
    protected FunctionSymbol lift(FunctionSymbol f, int i) {
        AnnotatedFunctionSymbol liftedAFS = new AnnotatedFunctionSymbol(f, i);
        FunctionSymbol liftedFS = this.fSMapper.getFS(liftedAFS);
        if (liftedFS == null) {
            liftedFS = this.funcSymbGen.getFresh(f.getName(), f.getArity());
            this.fSMapper.set(liftedFS, liftedAFS);
        }

        return this.fSMapper.getFS(liftedAFS);
    }

    /*
     * returns the function symbol representing f_i(lift(arg_1, i),---,lift(arg_n, i)) for parameters f(arg_1,...,arg_n) and i
     */
    protected TRSTerm lift(TRSTerm t, int i) {
        if (!(t instanceof TRSFunctionApplication)) {
            return t;
        }
        TRSFunctionApplication fA = (TRSFunctionApplication) t;
        FunctionSymbol root = fA.getRootSymbol();
        FunctionSymbol liftedRoot = this.lift(root, i);
        List<TRSTerm> args = fA.getArguments();
        List<TRSTerm> liftedArgs = new ArrayList<TRSTerm>();
        for (TRSTerm arg : args) {
            TRSTerm liftedArg = this.lift(arg, i);
            liftedArgs.add(liftedArg);
        }
        return TRSTerm.createFunctionApplication(liftedRoot, liftedArgs);
    }

    /*
     * returns f for a function symbol representing f_i
     */
    protected FunctionSymbol base(FunctionSymbol f) {
        AnnotatedFunctionSymbol aFS = this.fSMapper.getAFS(f);

        if (Globals.useAssertions) {
            assert (aFS != null);
            assert (aFS.f != null);
        }

        return this.fSMapper.getAFS(f).f;
    }

    protected TRSTerm base(TRSTerm t) {
        if (t.isVariable()) {
            return t;

        } else {
            TRSFunctionApplication fA = (TRSFunctionApplication) t;
            FunctionSymbol rootSymbol = fA.getRootSymbol();
            ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
            for (TRSTerm arg : fA.getArguments()) {
                newArgs.add(this.base(arg));
            }

            FunctionSymbol newRoot = this.base(rootSymbol);

            return TRSTerm.createFunctionApplication(newRoot, newArgs);
        }
    }

    protected Rule base(Rule r) {
        TRSFunctionApplication newLeft = (TRSFunctionApplication) this.base(r.getLeft());
        TRSTerm newRight = this.base(r.getRight());
        return Rule.create(newLeft, newRight);
    }

    /*
     * returns i for a function symbol representing f_i
     */
    protected int height(FunctionSymbol f) {
        AnnotatedFunctionSymbol aFS = this.fSMapper.getAFS(f);

        if (Globals.useAssertions) {
            assert (aFS != null);
            assert (aFS.f != null);
        }

        return aFS.nr;
    }

    /*
     * returns a maximal Set S of terms builded over signature such that for every s element S: base(s) = t
     */
    protected Set<TRSTerm> buildTermsWithSameBase(TRSTerm t, Set<FunctionSymbol> signature) {
        Set<TRSTerm> returnSet = new LinkedHashSet<TRSTerm>();
        if (t.isVariable()) {
            returnSet.add(t);
            return returnSet;
        } else {
            TRSFunctionApplication fA = (TRSFunctionApplication) t;
            Set<ArrayList<TRSTerm>> possibleArgs = new LinkedHashSet<ArrayList<TRSTerm>>();
            possibleArgs.add(new ArrayList<TRSTerm>());
            for (TRSTerm arg : fA.getArguments()) {
                Set<TRSTerm> possibleArg = this.buildTermsWithSameBase(arg, signature);
                Set<ArrayList<TRSTerm>> newPossibleArgs = new LinkedHashSet<ArrayList<TRSTerm>>(t.getSize());
                for (ArrayList<TRSTerm> args : possibleArgs) {
                    for (TRSTerm newArg : possibleArg) {
                        ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(args);
                        newArgs.add(newArg);
                        newPossibleArgs.add(newArgs);
                    }

                }
                possibleArgs = newPossibleArgs;
            }

            FunctionSymbol root = fA.getRootSymbol();
            for (FunctionSymbol newRoot : signature) {
                if (root.equals(this.base(newRoot))) {
                    for (ArrayList<TRSTerm> args : possibleArgs) {
                        returnSet.add(TRSTerm.createFunctionApplication(newRoot, ImmutableCreator.create(args)));
                    }
                }
            }

        }
        return returnSet;
    }

    /*
     * returns the size of t, where variables doesn't count, i.e. |x| = 0 for every variable x
     * and |f(t1, ..., tn)| = 1 + |t1| + ... + |tn|
     */
    private int sizeWRTFS(TRSTerm t) {
        int sum = 0;
        Map<FunctionSymbol, Integer> fSCount = t.getFunctionSymbolCount();
        for (Map.Entry<FunctionSymbol, Integer> entry : fSCount.entrySet()) {
            sum += entry.getValue();
        }

        return sum;
    }
}
