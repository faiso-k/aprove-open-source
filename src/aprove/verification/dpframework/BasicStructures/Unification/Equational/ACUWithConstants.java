/*
 * Created on Feb 10, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.Equational.Problems.*;
import aprove.verification.dpframework.BasicStructures.Unification.Equational.Utility.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 *  Unification algorithm ACU unification with constants.
 *
 *  Herold/Siekmann: "Unification in Abelian Semigroups", JAR 3, pp 247--283
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class ACUWithConstants extends UnificationWithConstants {

    private List<TRSVariable> oldVars;
    private List<TRSVariable> newVars;
    private List<TRSTerm> newTerms;
    private FunctionSymbol f;
    private List<List<IntVector>> unifierLists;
    private boolean trivial;

    public List<TRSVariable> getOldVars() {
        return this.oldVars;
    }

    public List<TRSVariable> getNewVars() {
        return this.newVars;
    }

    public List<TRSTerm> getNewTerms() {
        return this.newTerms;
    }

    public FunctionSymbol getF() {
        return this.f;
    }

    public List<List<IntVector>> getUnifierLists() {
        return this.unifierLists;
    }

    /** Returns a complete minimal set of unifiers if s and t are
     * unifiable, returns an empty set otherwise.
     */
    @Override
    public Collection<TRSSubstitution> unify(TRSTerm s, TRSTerm t, Set<TRSVariable> W) {
        return this.unify(s, t, W, true);
    }

    public boolean isTrivial() {
        return this.trivial;
    }

    /** Construct specifies weather the substitution should be constructed.
     */
    public Collection<TRSSubstitution> unify(TRSTerm s, TRSTerm t, Set<TRSVariable> W, boolean construct) {
        this.trivial = false;
        Stack<TRSSubstitution> res = new Stack<TRSSubstitution>();

        ACUWithConstantsProblem problem = ACUWithConstantsProblem.create(s, t);

        if(problem.isTrivial()) {
            this.trivial = true;
            if(construct) {
                Set<TRSVariable> V = new HashSet<TRSVariable>(s.getVariables());
                V.addAll(t.getVariables());
                TRSSubstitution id = TRSSubstitution.create();
                res.add(ElementaryUnification.baseAway(id, V, W));
            }
            return res;
        }

        this.f = problem.getFunctionSymbol();

        IntVector intVec = problem.getIntVector();

        IntVector hom = problem.getHom();
        DioHom diohom = DioHom.create(hom);

        /* solutions of the homogeneous equation */
        List<IntVector> homSol = new ArrayList<IntVector>(diohom.solutions());

        this.oldVars = problem.getVariableList();
        List<TRSTerm> constants = problem.getConstantList();
        this.newVars = new ArrayList<TRSVariable>();
        this.newTerms = new ArrayList<TRSTerm>();

        /* new variables are v_number */
        FreshVarGenerator fvg = new FreshVarGenerator(W);

        String prefix = "v";

        int newVarCount = homSol.size();
        for(int i = 0; i < newVarCount; i++) {
            this.newVars.add(fvg.getFreshVariable(TRSTerm.createVariable(prefix), false));
        }

        /* add the new variables and constants */
        this.newTerms.addAll(this.newVars);
        this.newTerms.addAll(constants);

        /* L = number of constants */
        int L = intVec.size() - hom.size();

        if(L == 0) {
            /* no constants */
            this.unifierLists = new ArrayList<List<IntVector>>();
            this.unifierLists.add(homSol);
            if(construct) {
                res.add(this.construct(homSol, this.oldVars, this.newTerms, this.f));
            }
        }
        else {
            /* get solutions to inhomogeneous equations */
            ArrayList<List<IntVector>> collect = new ArrayList<List<IntVector>>();

            for(TRSTerm tt : constants) {
                DioInhom dioinhom = DioInhom.create(hom, -problem.getConstantCount(tt));
                collect.add(dioinhom.specialSolutions());
            }

            /* cartesian product of these */
            ArrayList<ArrayList<IntVector>> product = this.product((ArrayList<List<IntVector>>)collect.clone());
            this.unifierLists = new ArrayList<List<IntVector>>();

            for(List<IntVector> v : product) {
                List<IntVector> l = new ArrayList<IntVector>(homSol);
                l.addAll(v);
                this.unifierLists.add(l);
                /* construct solution */
                if(construct) {
                    res.add(this.construct(l, this.oldVars, this.newTerms, this.f));
                }
            }
        }

        return res;
    }


    /** constructs a substitution from IntVectors */
    private TRSSubstitution construct(List<IntVector> sol, List<TRSVariable> oldVars, List<TRSTerm> newTerms, FunctionSymbol f) {
        TRSSubstitution res = TRSSubstitution.create();

        int ni = 0;

        /* for each "old" variable... */
        for(TRSVariable v : oldVars) {
            /* ...construct a list of the arguments it is mapped to */
            List<TRSTerm> args = new ArrayList<TRSTerm>();
            int nj = 0;
            for(IntVector intVec : sol) {
                TRSTerm tt = (TRSTerm)newTerms.get(nj);
                for(int k=0; k<intVec.get(ni); k++) {
                    args.add(tt);
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
        if(args.size()==0) {
            throw new RuntimeException("no unit in ACUWithConstants");
        }
        if(args.size()==1) {
            /* no app of f */
            return args.get(0);
        }

        ArrayList<TRSTerm> resArgs = new ArrayList<TRSTerm>(2);
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

    /* cartesian product of the lists in v */
    private ArrayList<ArrayList<IntVector>> product(ArrayList<List<IntVector>> v) {
        if(v.size()==1) {
            return this.vectorize(v);
        }

        ArrayList<ArrayList<IntVector>> res = new ArrayList<ArrayList<IntVector>>();
        ArrayList<IntVector> w = (ArrayList<IntVector>)v.get(0);
        v.remove(0);

        /* construct cartesian product of the remaining lists */
        ArrayList<ArrayList<IntVector>> r = this.product(v);

        for(IntVector o : w) {
            for(ArrayList<IntVector> rr : r) {
                /* add o to all products of the rest */
                ArrayList<IntVector> rrr = new ArrayList<IntVector>();
                rrr.add(o);
                rrr.addAll(rr);
                res.add(rrr);
            }
        }

        return res;
    }

    /* each element of v is put into a list of its own */
    private ArrayList<ArrayList<IntVector>> vectorize(ArrayList<List<IntVector>> v) {
        ArrayList<ArrayList<IntVector>> res = new ArrayList<ArrayList<IntVector>>();
        ArrayList<IntVector> w = (ArrayList<IntVector>)v.get(0);

        for(IntVector o : w) {
            ArrayList<IntVector> r = new ArrayList<IntVector>();
            r.add(o);
            res.add(r);
        }

        return res;
    }

    @Override
    public boolean areTheoryUnifiable(TRSTerm s, TRSTerm t) {
        /* ACU unify s and t */
        HashSet<TRSVariable> W = new HashSet<TRSVariable>(s.getVariables());
        W.addAll(t.getVariables());
        this.unify(s, t, W, false);

        return !this.getUnifierLists().isEmpty();
    }

}

