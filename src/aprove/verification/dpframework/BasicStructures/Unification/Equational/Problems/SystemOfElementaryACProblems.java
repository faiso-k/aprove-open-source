/*
 * Created on Feb 16, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational.Problems;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.Equational.Utility.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 *  Representation of a system of elementary AC unification problems.
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class SystemOfElementaryACProblems implements SystemOfElementaryProblems {

    private Set<TRSVariable> absVars;
    private List<PairOfACTerms> l;
    private FunctionSymbol fun;
    private FreshVarGenerator fvg;
    private Set<FunctionSymbol> acSig;
    private List<ACTerm> termlist;
    private List<ACTerm> constlist;
    private List<IntVector> A;
    private BoolVector constrain;   // variables that have to have value at most 1
    private int varCount;
    private int n;
    private boolean trivial;

    private SystemOfElementaryACProblems(List<PairOfACTerms> l, FunctionSymbol f, Set<TRSVariable> absVars, FreshVarGenerator fvg, Set<FunctionSymbol> acSig) {
        this.l = l;
        this.fun = f;
        this.absVars = absVars;
        this.fvg = fvg;
        this.acSig = acSig;
        this.construct();
    }

    private void construct() {
        SortedSet<ACTerm> terms = new TreeSet<ACTerm>(new ACTermComparator(this.absVars));
        /* construct term list */
        for(PairOfACTerms pair:this.l) {
            MultisetOfACTerms restLeft = pair.getLeft().getMultiargs().subtract(pair.getRight().getMultiargs());
            MultisetOfACTerms restRight = pair.getRight().getMultiargs().subtract(pair.getLeft().getMultiargs());

            terms.addAll(restLeft.elements());
            terms.addAll(restRight.elements());

        }
        this.termlist = new ArrayList<ACTerm>(terms);

        /* construct matrix of diophantine system */
        this.A = new ArrayList<IntVector>();
        this.n = this.termlist.size();
        for(PairOfACTerms pair:this.l) {
            int[] tmp = new int[this.n];

            int count = 0;
            for(ACTerm tt:this.termlist) {
                tmp[count] = pair.getLeft().getMultiargs().numberOfOccurences(tt) - pair.getRight().getMultiargs().numberOfOccurences(tt);
                count++;
            }

            this.A.add(IntVector.create(tmp, 0));
        }

        /* determine constrained components */
        boolean con[] = new boolean[this.n];
        boolean isconst[] = new boolean[this.n];
        int count = 0;
        for(ACTerm tt:this.termlist) {
            if(tt.isConstant()) {
                /* a constant is constrained a well */
                con[count] = true;
                isconst[count] = true;
            }
            else {
                isconst[count] = false;
                if(this.absVars.contains(tt.toTerm())) {
                    con[count] = true;
                }
                else {
                    con[count] = false;
                }
            }
            count++;
        }
        this.constrain = BoolVector.create(con, 0);

        this.trivial = this.termlist.isEmpty();
        this.varCount = this.getVarCount();

        this.constlist = new ArrayList<ACTerm>();
        for(int j=this.varCount; j<this.n; j++) {
            this.constlist.add(this.termlist.get(j));
        }
    }

    private int getVarCount() {
        int res = 0;
        boolean hasVar = true;
        Iterator<ACTerm> i = this.termlist.iterator();
        while(i.hasNext() && hasVar) {
            ACTerm tt = i.next();
            if(tt.isVariable()) {
                res++;
            }
            else {
                hasVar = false;
            }
        }
        return res;
    }

    /** Creates a new SystemOfElementaryACProblems. */
    public static SystemOfElementaryACProblems create(List<PairOfACTerms> l, FunctionSymbol f, Set<TRSVariable> absVars, FreshVarGenerator fvg, Set<FunctionSymbol> acSig) {
        return new SystemOfElementaryACProblems(l, f, absVars, fvg, acSig);
    }

    public boolean isTrivial() {
        return this.trivial;
    }

    /** Returns the list of terms of this SystemOfElementaryACProblems.
     */
    public List<ACTerm> getTermList() {
        return this.termlist;
    }

    /** Returns the list of variables of this SystemOfElementaryACProblems.
     */
    public List<ACTerm> getVariableList() {
        List<ACTerm> res = new ArrayList<ACTerm>();

        for(int i= 0; i<this.varCount; i++) {
            res.add(this.termlist.get(i));
        }

        return res;
    }


    /** Returns the List<IntVector> associated to this SystemOfElementaryACProblems.
     */
    public List<IntVector> getIntVectors() {
        return this.A;
    }


    public FunctionSymbol getFunctionSymbol() {
        return this.fun;
    }


    /** Returns a list containing the quasi solved forms.
     */
    @Override
    public List<List<PairOfACTerms>> getQuasiSolvedForms() {
        DioHomSystem system = DioHomSystem.create(this.A, this.constrain);

        /* the solutions have components at most 1 for alien terms and constants */
        List<IntVector> sol = system.solutions();
        List<IntVector> filtered = new ArrayList<IntVector>();
        for(IntVector s:sol) {
            /* for constants, exactly one component may be non-null */
            boolean OK = true;
            boolean hasNonnull = false;
            int j=this.varCount;
            while(j<this.n && OK) {
                if(s.get(j)!=0) {
                    if(hasNonnull) {
                        OK = false;
                    }
                    hasNonnull = true;
                }
                j++;
            }
            if(OK) {
                filtered.add(s);
            }
        }

        /* new variables are v_number */
        ArrayList<ACTerm> newTerms = new ArrayList<ACTerm>();

        HashMap<ACTerm, ArrayList<IntVector>> consties = new HashMap<ACTerm, ArrayList<IntVector>>();
        for(ACTerm t:this.constlist) {
            consties.put(t, new ArrayList<IntVector>());
        }

        sol = new ArrayList<IntVector>();
        String prefix = "v";

        for(IntVector s:filtered) {
            int j = this.varCount;
            boolean found = false;
            while(j < this.n) {
                if(s.get(j)!=0) {
                    ACTerm consta = this.termlist.get(j);
                    consties.get(consta).add(s);
                    found = true;
                }
                j++;
            }
            if(!found) {
                sol.add(s);
                newTerms.add(ACTerm.create(this.fvg.getFreshVariable(TRSTerm.createVariable(prefix), false), this.acSig));
            }
        }

        for(ACTerm consta:this.constlist) {
            List<IntVector> next = consties.get(consta);;
            sol.addAll(next);
            for(int k=0; k<next.size(); k++) {
                newTerms.add(consta);
            }
        }

        /* varBoolSol contains information about the solutions to the variable part */
        List<BoolVector> varBoolSol = new ArrayList<BoolVector>();
        boolean[] bsol = new boolean[sol.size()];
        Iterator<IntVector> i = sol.iterator();
        int ni = 0;
        while(ni < sol.size()) {
            varBoolSol.add(BoolVector.create(i.next()));;
            bsol[ni] = false;
            ni++;
        }
        BoolVector boolSol = BoolVector.create(bsol, 0);

        /* get all sublists of varSol s.t. each row contains an entry != 0 */
        boolean[] tmp = new boolean[this.n];
        for(int j=0; j<this.n; j++) {
            tmp[j] = false;
        }
        BoolVector isPos = BoolVector.create(tmp, 0);
        List<BoolVector> allSols = this.filterConstrained(this.getAllSols(boolSol, varBoolSol, isPos), sol);

        /* transform into quasi-solved forms */
        List<List<PairOfACTerms>> res = new ArrayList<List<PairOfACTerms>>();
        for(BoolVector next:allSols) {
            res.add(this.constructQuasiSolvedForm(next, sol, newTerms));
        }

        return res;

    }


    /* computes the sublists of varSol yielding a valid substitution */
    private List<BoolVector> getAllSols(BoolVector boolSol, List<BoolVector> varBoolSol, BoolVector isPos) {
        List<BoolVector> res = new ArrayList<BoolVector>();
        int n = boolSol.size();
        int val = boolSol.getValue();
        int m = n - val;
        boolean pos = isPos.isTrue();

        if(m==0) {
            if(pos) {
            /* OK! */
                res.add(boolSol);
            }
            return res;
        }

        if(pos) {
            /* everything is possible! */
            for (Sequence sss : SequenceGenerator.create(m, 2)) {
                BoolVector resi = boolSol.deepcopy();
                for(int c=0; c<m; c++) {
                    if(sss.get(c)==1) {
                        resi.set(val + c, true);
                    }
                    else {
                        resi.set(val + c, false);
                    }
                }
                res.add(resi);
            }
        }
        else {
            Iterator<BoolVector> i = varBoolSol.subList(val, n).iterator();
            /* add one entry */
            for(int k=val; k<n; k++) {
                BoolVector newBoolSol = boolSol.deepcopy();
                newBoolSol.setValue(k+1);
                newBoolSol.set(k, true);
                BoolVector newIsPos = isPos.disj(i.next());
                /* and get solutions for this */
                res.addAll(this.getAllSols(newBoolSol, varBoolSol, newIsPos));
            }
        }

        return res;
    }

    /* returns the elements of input that satisfy the alien term condition */
    private List<BoolVector> filterConstrained(List<BoolVector> input, List<IntVector> sol) {
        List<BoolVector> res = new ArrayList<BoolVector>();
        for(BoolVector cand:input) {
            /* small enough? */
            IntVector sum = IntVector.createZero(this.n);
            for(int j=0; j<cand.size(); j++) {
                if(cand.get(j)) {
                    sum = sum.add(sol.get(j));
                }
            }
            boolean OK = true;
            for(int j=0; j<sum.size(); j++) {
                if(this.constrain.get(j) && sum.get(j)>1) {
                    OK = false;
                }
            }
            if(OK) {
                res.add(cand);
            }
        }

        return res;
    }


    /* computes a quasi-solved form corresponding to an BoolVector */
    private List<PairOfACTerms> constructQuasiSolvedForm(BoolVector bv, List<IntVector> sol, List<ACTerm> newTerms) {
        List<PairOfACTerms> res = new ArrayList<PairOfACTerms>();
        for(int i=0; i<this.varCount; i++) {
            /* for each variable */
            ArrayList<ACTerm> args = new ArrayList<ACTerm>();
            for(int j=0; j<bv.size(); j++) {
                if(bv.get(j)) {
                    ACTerm t = newTerms.get(j);
                    int n = sol.get(j).get(i);
                    if(n!=0) {
                        for(int k=0;k<n;k++) {
                            args.add(t);
                        }
                    }
                }
            }
            res.add(this.constructACTermPair(this.termlist.get(i), MultisetOfACTerms.create(args)));
        }

        return res;
    }

    /* returns a pair of ACTerms */
    private PairOfACTerms constructACTermPair(ACTerm var, MultisetOfACTerms args) {
        ACTerm right;
        if(args.realSize()==1) {
            right = args.elements().iterator().next();
        }
        else {
            right = ACTerm.create(this.fun, args, this.acSig);
        }
        return PairOfACTerms.create(var, right);
    }


    @Override
    public String toString() {
        StringBuffer res = new StringBuffer(this.termlist.toString());
        res.append("\n");

        Iterator i = this.A.iterator();
        while(i.hasNext()) {
            res.append(i.next());
            if(i.hasNext()) {
            res.append("\n");
            }
        }

        return res.toString();
    }

// BEGIN iterator stuff

    private List<IntVector> soli;
    private List<BoolVector> varBoolSoli;
    private List<ACTerm> newTermsi;

    /** Returns an iterator that generates the quasi solved forms one-bq-one.
     */
    @Override
    public Iterator<List<PairOfACTerms>> iterateQuasiSolvedForms() {
        this.setUpIterator();
        return new solIterator(this.soli, this.varBoolSoli, this.constrain, this.newTermsi, this.n);
    }

    private void setUpIterator() {
        DioHomSystem system = DioHomSystem.create(this.A, this.constrain);

        /* the solutions have components at most 1 for alien terms and constants */
        this.soli = system.solutions();
        List<IntVector> filtered = new ArrayList<IntVector>();
        for(IntVector s:this.soli) {
            /* for constants, exactly one component may be non-null */
            boolean OK = true;
            boolean hasNonnull = false;
            int j=this.varCount;
            while(j<this.n && OK) {
                if(s.get(j)!=0) {
                    if(hasNonnull) {
                        OK = false;
                    }
                    hasNonnull = true;
                }
                j++;
            }
            if(OK) {
                filtered.add(s);
            }
        }

        /* new variables are v_number */
        this.newTermsi = new ArrayList<ACTerm>();


        HashMap<ACTerm, ArrayList<IntVector>> consties = new HashMap<ACTerm, ArrayList<IntVector>>();
        for(ACTerm t:this.constlist) {
            consties.put(t, new ArrayList<IntVector>());
        }

        this.soli = new ArrayList<IntVector>();
        String prefix = "v";

        for(IntVector s:filtered) {
            int j = this.varCount;
            boolean found = false;
            while(j < this.n) {
                if(s.get(j)!=0) {
                    ACTerm consta = this.termlist.get(j);
                    consties.get(consta).add(s);
                    found = true;
                }
                j++;
            }
            if(!found) {
                this.soli.add(s);
                this.newTermsi.add(ACTerm.create(this.fvg.getFreshVariable(TRSTerm.createVariable(prefix), false), this.acSig));
            }
        }

        for(ACTerm consta:this.constlist) {
            List<IntVector> next = consties.get(consta);
            this.soli.addAll(next);
            for(int k=0; k<next.size(); k++) {
                this.newTermsi.add(consta);
            }
        }

        /* varBoolSoli contains information about the solutions to the variable part */
        this.varBoolSoli = new ArrayList<BoolVector>();
        Iterator<IntVector> i = this.soli.iterator();
        int ni = 0;
        while(ni < this.soli.size()) {
            this.varBoolSoli.add(BoolVector.create(i.next()));;
            ni++;
        }
    }


    private class solIterator implements Iterator<List<PairOfACTerms>> {
        private boolean hasNext;
        private List<PairOfACTerms> next;
        private Iterator<Sequence> seq;
        private List<IntVector> sol;
        private List<BoolVector> boolSol;
        private List<ACTerm> newTerms;
        private BoolVector constrain;
        private int n, m;

        private boolean isValid(Sequence s) {
            boolean[] b = new boolean[this.n];
            for(int i=0; i<this.n; i++) {
                b[i] = false;
            }
            BoolVector bv = BoolVector.create(b, 0);
            for(int i=0; i<this.m; i++) {
                if(s.get(i)==1) {
                    bv = bv.disj(this.boolSol.get(i));
                }
            }
            if(!bv.isTrue()) {
                return false;
            }
            else {
            /* small enough? */
                IntVector sum = IntVector.createZero(this.n);
                for(int j=0; j<this.m; j++) {
                    if(s.get(j)==1) {
                        sum = sum.add(this.sol.get(j));
                    }
                }
                boolean OK = true;
                for(int j=0; j<this.n; j++) {
                    if(this.constrain.get(j) && sum.get(j)>1) {
                        OK = false;
                    }
                }
                return OK;
            }
        }

        public solIterator(List<IntVector> sol, List<BoolVector> boolSol, BoolVector constrain, List<ACTerm> newTerms, int n) {
            this.sol = sol;
            this.boolSol = boolSol;
            this.constrain = constrain;
            this.newTerms = newTerms;
            this.n = n;
            this.m = newTerms.size();
            this.hasNext = false;
            this.next = null;
            this.seq = SequenceGenerator.create(this.m, 2).iterator();
            while(this.seq.hasNext() && !this.hasNext()) {
                Sequence s = this.seq.next();
                if(this.isValid(s)) {
                    this.hasNext = true;
                    this.next = this.construct(s);
                }
            }
        }

        @Override
        public boolean hasNext() {
            return this.hasNext;
        }

        @Override
        public List<PairOfACTerms> next() {
            List<PairOfACTerms> res = this.next;
            this.hasNext = false;
            while(this.seq.hasNext() && !this.hasNext()) {
                Sequence s = this.seq.next();
                if(this.isValid(s)) {
                    this.hasNext = true;
                    this.next = this.construct(s);
                }
            }
            return res;
        }

        private List<PairOfACTerms> construct(Sequence s) {
            boolean tmp[] = new boolean[s.size()];
            for(int i=0; i<s.size(); i++) {
                tmp[i] = (s.get(i)==1);
            }
            BoolVector bv = BoolVector.create(tmp, 0);
            return SystemOfElementaryACProblems.this.constructQuasiSolvedForm(bv, this.sol, this.newTerms);
        }


        @Override
        public void remove() {
            throw new UnsupportedOperationException("");
        }

    }




    /* Comparator that places variables before constants and sorts like symbols according to their name */
    private class ACTermComparator implements Comparator<ACTerm> {

        private Set<TRSVariable> absVars;

        public ACTermComparator(Set<TRSVariable> absVars) {
            super();
            this.absVars = absVars;
        }

        @Override
        public int compare(ACTerm s, ACTerm t) {

            if(s.isVariable()) {
                if(t.isVariable()) {
                    if(this.absVars.contains(s.toTerm())) {
                        if(this.absVars.contains(t.toTerm())) {
                            return s.toString().compareTo(t.toString());
                        }
                        else {
                            return 1;
                        }
                    }
                    else {
                        if(this.absVars.contains(t.toTerm())) {
                            return -1;
                        }
                        else {
                            return s.toString().compareTo(t.toString());
                        }
                    }
                }
                else {
                    return -1;
                }
            }
            else {
                if(t.isVariable()) {
                    return 1;
                }
                else {
                    return s.toString().compareTo(t.toString());
                }
            }
        }

    }

}

