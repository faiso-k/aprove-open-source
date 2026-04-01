package aprove.verification.oldframework.Unification;

import java.util.*;

import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Unification.Utility.*;

/**
 *  Unification algorithm for AC unification with constants.
 *  <p>
 *  Herold/Siekmann: "Unification in Abelian Semigroups", JAR 3, pp 247--283
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class ACWithConstants extends UnificationWithConstants {

    /** Returns a set complete minimal set of unifiers if s and t are
     * unifiable, returns an empty set otherwise.
     */
    @Override
    public Collection<AlgebraSubstitution> unify(AlgebraTerm s, AlgebraTerm t, Set<AlgebraVariable> W) {
    Stack<AlgebraSubstitution> res = new Stack<AlgebraSubstitution>();

    ACUWithConstants acu = new ACUWithConstants();

    /* ACU unify s and t */
    acu.unify(s, t, W, false);

    if(acu.isTrivial()) {
        Set<AlgebraVariable> V = new HashSet<AlgebraVariable>(s.getVars());
        V.addAll(t.getVars());
        AlgebraSubstitution id = AlgebraSubstitution.create();
        res.add(ElementaryUnification.baseAway(id, V, W));
        return res;
    }

    List<AlgebraVariable> oldVars = acu.getOldVars();
    List<AlgebraVariable> newVars = acu.getNewVars();
    List<AlgebraTerm> newTerms = acu.getNewTerms();
    SyntacticFunctionSymbol f = acu.getF();

    int newVarsCount = newVars.size();

    /* get unifiers as matrices */
    List sols = acu.getUnifierLists();

    /* extract all AC unifiers from any ACU unifier */
    Iterator i = sols.iterator();
    while(i.hasNext()) {
        List<IntVector> sol = (List<IntVector>)i.next();
        res.addAll(this.extractAll(sol, oldVars, newTerms, newVarsCount, f));
    }

    return res;

    }

    /* extracts all AC unifiers from an ACU unifier */
    private Set<AlgebraSubstitution> extractAll(List<IntVector> sol, List<AlgebraVariable> oldVars, List<AlgebraTerm> newTerms, int newVarsCount, SyntacticFunctionSymbol f) {
    Set<AlgebraSubstitution> res = new HashSet<AlgebraSubstitution>();

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
    List<BoolVector> varBoolSol = new Vector<BoolVector>();
    boolean[] bsol = new boolean[newVarsCount];
    Iterator i = sol.iterator();
    int ni = 0;
    while(ni < newVarsCount) {
        varBoolSol.add(BoolVector.create((IntVector)i.next()));;
        bsol[ni] = false;
        ni++;
    }

    BoolVector boolSol = BoolVector.create(bsol, 0);

    /* get all sublists of varSol s.t. each row contains an entry != 0 */
    List<BoolVector> allSols = this.getAllSols(boolSol, varBoolSol, constBoolVec);

    /* transform sol into termlists */
    List termSol = new Vector();
    i = sol.iterator();
    Iterator j = newTerms.iterator();
    ni = 0;
    while(ni < size) {
        termSol.add(this.constructTermSol((IntVector)i.next(), (AlgebraTerm)j.next(), f));
        ni++;
    }

    /* transform into substitutions */
    i = allSols.iterator();
    while(i.hasNext()) {
        res.add(this.construct(termSol, (BoolVector)i.next(), oldVars, f));
    }

    return res;
    }

    /* computes the sublists of varSol yielding a valid substitution */
    private List<BoolVector> getAllSols(BoolVector boolSol, List<BoolVector> varBoolSol, BoolVector constBoolVec) {
    List<BoolVector> res = new Vector<BoolVector>();
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
    private List constructTermSol(IntVector sol, AlgebraTerm newTerm, SyntacticFunctionSymbol f) {
    Vector res = new Vector();

    for(int i=0; i<sol.size(); i++) {
        int n = sol.get(i);
        List<AlgebraTerm> args = new Vector<AlgebraTerm>();
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
    private AlgebraSubstitution construct(List termSol, BoolVector use, List<AlgebraVariable> oldVars, SyntacticFunctionSymbol f) {
    AlgebraSubstitution res = AlgebraSubstitution.create();

    Iterator i = oldVars.iterator();
    int ni = 0;

    /* for each "old" variable... */
    while(i.hasNext()) {
        /* ...construct a list of the arguments it is mapped to */
        AlgebraVariable v = (AlgebraVariable)i.next();
        List<AlgebraTerm> args = new Vector<AlgebraTerm>();
        Iterator j = termSol.iterator();
        int nj = 0;
        while(j.hasNext()) {
        List termVec = (List)j.next();
        if(use.get(nj)) {
            Object tt = termVec.get(ni);
            if(tt!=null) {
                args.add((AlgebraTerm)tt);
            }
        }
        nj++;
        }
        /* get a term containing the arguments */
        res.put((VariableSymbol)v.getSymbol(), this.constructTerm(f, args));
        ni++;
    }

    return res;
    }

    /* construct a term from a list of arguments */
    private AlgebraTerm constructTerm(SyntacticFunctionSymbol f, List args) {
    if(args.size()==1) {
        /* no app of f */
        return (AlgebraTerm)args.get(0);
    }

    Vector<AlgebraTerm> resArgs = new Vector<AlgebraTerm>();
    if(args.size()==2) {
        /* f(x, y) */
        resArgs.add((AlgebraTerm)args.get(0));
        resArgs.add((AlgebraTerm)args.get(1));
    }
    else {
        /* f(x, t) where t is computed recursively */
        resArgs.add((AlgebraTerm)args.get(0));
        resArgs.add(this.constructTerm(f, args.subList(1, args.size())));
        }
    return AlgebraFunctionApplication.create(f, resArgs);
    }

    @Override
    public boolean areTheoryUnifiable(AlgebraTerm s, AlgebraTerm t) {
    boolean res = false;
    ACUWithConstants acu = new ACUWithConstants();

    /* ACU unify s and t */
    HashSet<AlgebraVariable> W = new HashSet<AlgebraVariable>(s.getVars());
    W.addAll(t.getVars());
    acu.unify(s, t, W, false);

    if(acu.isTrivial()) {
        return true;
    }

    /* get unifiers as matrices */
    List sols = acu.getUnifierLists();

    /* it suffices that the sum of all rows of one matrix is positive */
    Iterator i = sols.iterator();
    while(i.hasNext() && !res) {
        List<IntVector> sol = (List<IntVector>)i.next();
        if(this.disjAll(sol).isTrue()) {
        res = true;
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
