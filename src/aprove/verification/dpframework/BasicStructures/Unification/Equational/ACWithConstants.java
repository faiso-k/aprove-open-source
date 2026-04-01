/*
 * Created on Feb 10, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.Equational.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 *  Unification algorithm for AC unification with constants.
 *  <p>
 *  Herold/Siekmann: "Unification in Abelian Semigroups", JAR 3, pp 247--283
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class ACWithConstants extends UnificationWithConstants {

    public ACWithConstants(){

    }

    /** Returns a set complete minimal set of unifiers if s and t are
     * unifiable, returns an empty set otherwise.
     */
    @Override
    public Collection<TRSSubstitution> unify(TRSTerm s, TRSTerm t, Set<TRSVariable> W) {
        Stack<TRSSubstitution> res = new Stack<TRSSubstitution>();

        ACUWithConstants acu = new ACUWithConstants();

        /* ACU unify s and t */
        acu.unify(s, t, W, false);

        if(acu.isTrivial()) {
            Set<TRSVariable> V = new HashSet<TRSVariable>(s.getVariables());
            V.addAll(t.getVariables());
            TRSSubstitution id = TRSSubstitution.create();
            res.add(ElementaryUnification.baseAway(id, V, W));
            return res;
        }

        List<TRSVariable> oldVars = acu.getOldVars();
        List<TRSVariable> newVars = acu.getNewVars();
        List<TRSTerm> newTerms = acu.getNewTerms();
        FunctionSymbol f = acu.getF();

        int newVarsCount = newVars.size();

        /* get unifiers as matrices */
        List<List<IntVector>> sols = acu.getUnifierLists();

        /* extract all AC unifiers from any ACU unifier */
        for(List<IntVector> sol : sols) {
            res.addAll(this.extractAll(sol, oldVars, newTerms, newVarsCount, f));
        }

        return res;
    }

    /* extracts all AC unifiers from an ACU unifier */
    private Set<TRSSubstitution> extractAll(List<IntVector> sol, List<TRSVariable> oldVars, List<TRSTerm> newTerms, int newVarsCount, FunctionSymbol f) {
        Set<TRSSubstitution> res = new HashSet<TRSSubstitution>();

        int size = sol.size();
        int constCount = size - newVarsCount;
        List constSol = sol.subList(newVarsCount, size);

        BoolVector constBoolVec = null;

        /* let's see which restrictions we get from the constants */
        if(constCount!=0) {
            Iterator i = constSol.iterator();
            constBoolVec = BoolVector.create((IntVector)i.next());
            int ni = 1;
            while(ni < constCount) {
                constBoolVec = constBoolVec.disj(BoolVector.create((IntVector)i.next()));
                ni++;
            }
        }
        else {
            int n = oldVars.size();
            boolean[] tmp = new boolean[n];
            for(int i=0; i<n; i++) {
                tmp[i] = false;
            }
            constBoolVec = BoolVector.create(tmp, 0);
        }


        /* varBoolSol contains information about the solutions to the variable part */
        List<BoolVector> varBoolSol = new ArrayList<BoolVector>();
        boolean[] bsol = new boolean[newVarsCount];
        Iterator<IntVector> i = sol.iterator();
        int ni = 0;
        while(ni < newVarsCount) {
            varBoolSol.add(BoolVector.create(i.next()));;
            bsol[ni] = false;
            ni++;
        }

        BoolVector boolSol = BoolVector.create(bsol, 0);

        /* get all sublists of varSol s.t. each row contains an entry != 0 */
        List<BoolVector> allSols = this.getAllSols(boolSol, varBoolSol, constBoolVec);

        /* transform sol into termlists */
        List<List<TRSTerm>> termSol = new ArrayList<List<TRSTerm>>();
        i = sol.iterator();
        Iterator<TRSTerm> j = newTerms.iterator();
        ni = 0;
        while(ni < size) {
            termSol.add(this.constructTermSol(i.next(), j.next(), f));
            ni++;
        }

        /* transform into substitutions */
        Iterator<BoolVector> ib = allSols.iterator();
        while(ib.hasNext()) {
            res.add(this.construct(termSol, ib.next(), oldVars, f));
        }

        return res;
    }

    /* computes the sublists of varSol yielding a valid substitution */
    private List<BoolVector> getAllSols(BoolVector boolSol, List<BoolVector> varBoolSol, BoolVector constBoolVec) {
        List<BoolVector> res = new ArrayList<BoolVector>();
        int n = boolSol.size();
        int val = boolSol.getValue();
        int m = n - val;
        boolean pos = constBoolVec.isTrue();

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
            Iterator i = varBoolSol.subList(val, n).iterator();
            /* add one entry */
            for(int k=val; k<n; k++) {
                BoolVector newBoolSol = boolSol.deepcopy();
                newBoolSol.setValue(k+1);
                newBoolSol.set(k, true);
                /* start at k+1 in recursive calls */
                BoolVector newConstBoolVec = constBoolVec.disj((BoolVector)i.next());

                /* and get solutions for this */
                res.addAll(this.getAllSols(newBoolSol, varBoolSol, newConstBoolVec));
            }
        }

        return res;
    }


    /* constructs a list containing the terms corresponding to sol */
    private List<TRSTerm> constructTermSol(IntVector sol, TRSTerm newTerm, FunctionSymbol f) {
        ArrayList<TRSTerm> res = new ArrayList<TRSTerm>();

        for(int i=0; i<sol.size(); i++) {
            int n = sol.get(i);
            List<TRSTerm> args = new ArrayList<TRSTerm>();
            for(int j=0; j<n; j++) {
                args.add(newTerm);
            }
            if(n!=0) {
                res.add(this.constructTerm(f, args));
            }
            else {
                res.add(null);
            }
        }

        return res;
    }


    /* constructs a substitution from a BoolVector */
    private TRSSubstitution construct(List<List<TRSTerm>> termSol, BoolVector use, List<TRSVariable> oldVars, FunctionSymbol f) {
        TRSSubstitution res = TRSSubstitution.create();

        int ni = 0;

        /* for each "old" variable... */
        for(TRSVariable v : oldVars) {
            /* ...construct a list of the arguments it is mapped to */
            List<TRSTerm> args = new ArrayList<TRSTerm>();
            int nj = 0;
            for(List<TRSTerm> termVec:termSol) {
                if(use.get(nj)) {
                    TRSTerm tt = termVec.get(ni);
                    if(tt!=null) {
                        args.add(tt);
                    }
                }
                nj++;
            }
            /* get a term containing the arguments */
            res = res.extend(TRSSubstitution.create(v, this.constructTerm(f, args)));
            ni++;
        }

        return res;
    }

    /* construct a term from a list of arguments */
    private TRSTerm constructTerm(FunctionSymbol f, List<TRSTerm> args) {
        if(args.size()==1) {
            /* no app of f */
            return args.get(0);
        }

        ArrayList<TRSTerm> resArgs = new ArrayList<TRSTerm>();
        if(args.size()==2) {
            /* f(x, y) */
            resArgs.add(args.get(0));
            resArgs.add(args.get(1));
        }
        else {
            /* f(x, t) where t is computed recursively */
            resArgs.add(args.get(0));
            resArgs.add(this.constructTerm(f, args.subList(1, args.size())));
        }
        return TRSTerm.createFunctionApplication(f, ImmutableCreator.create(resArgs));
    }

    @Override
    public boolean areTheoryUnifiable(TRSTerm s, TRSTerm t) {
        boolean res = false;
        ACUWithConstants acu = new ACUWithConstants();

        /* ACU unify s and t */
        HashSet<TRSVariable> W = new HashSet<TRSVariable>(s.getVariables());
        W.addAll(t.getVariables());
        acu.unify(s, t, W, false);

        if(acu.isTrivial()) {
            return true;
        }

        /* get unifiers as matrices */
        List<List<IntVector>> sols = acu.getUnifierLists();

        /* it suffices that the sum of all rows of one matrix is positive */
        for(List<IntVector> sol:sols) {
            if(this.disjAll(sol).isTrue()) {
                res = true;
                return res;
            }
        }

        return res;
    }

    private BoolVector disjAll(List<IntVector> l) {
        Iterator i = l.iterator();
        BoolVector res = BoolVector.create((IntVector)i.next());
        while(i.hasNext()) {
            res = res.disj(BoolVector.create((IntVector)i.next()));
        }
        return res;
    }

}
