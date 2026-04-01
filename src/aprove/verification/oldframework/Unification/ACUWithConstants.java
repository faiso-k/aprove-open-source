package aprove.verification.oldframework.Unification;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Unification.Problems.*;
import aprove.verification.oldframework.Unification.Utility.*;
import aprove.verification.oldframework.Utility.*;

/**
 *  Unification algorithm ACU unification with constants.
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class ACUWithConstants extends UnificationWithConstants {

    private List<AlgebraVariable> oldVars;
    private List<AlgebraVariable> newVars;
    private List<AlgebraTerm> newTerms;
    private SyntacticFunctionSymbol f;
    private List unifierLists;
    private boolean trivial;

    public List<AlgebraVariable> getOldVars() {
    return this.oldVars;
    }

    public List<AlgebraVariable> getNewVars() {
    return this.newVars;
    }

    public List<AlgebraTerm> getNewTerms() {
    return this.newTerms;
    }

    public SyntacticFunctionSymbol getF() {
    return this.f;
    }

    public List getUnifierLists() {
    return this.unifierLists;
    }

    /** Returns a set complete minimal set of unifiers if s and t are
     * unifiable, returns an empty set otherwise.
     */
    @Override
    public Collection<AlgebraSubstitution> unify(AlgebraTerm s, AlgebraTerm t, Set<AlgebraVariable> W) {
    return this.unify(s, t, W, true);
    }

    public boolean isTrivial() {
    return this.trivial;
    }

    /** Construct specifies weather the substitution should be constructed.
     */
    public Collection<AlgebraSubstitution> unify(AlgebraTerm s, AlgebraTerm t, Set<AlgebraVariable> W, boolean construct) {
    this.trivial = false;
    Stack<AlgebraSubstitution> res = new Stack<AlgebraSubstitution>();

    ACUWithConstantsProblem problem = ACUWithConstantsProblem.create(s, t);

    if(problem.isTrivial()) {
        this.trivial = true;
        if(construct) {
        Set<AlgebraVariable> V = new HashSet<AlgebraVariable>(s.getVars());
        V.addAll(t.getVars());
            AlgebraSubstitution id = AlgebraSubstitution.create();
            res.add(ElementaryUnification.baseAway(id, V, W));
        }
        return res;
    }

    this.f = problem.getFunctionSymbol();

    IntVector intVec = problem.getIntVector();

    IntVector hom = problem.getHom();
    DioHom diohom = DioHom.create(hom);

    /* solutions of the homogeneous equation */
    List<IntVector> homSol = new Vector<IntVector>(diohom.solutions());

    this.oldVars = problem.getVariableList();
    List<AlgebraTerm> constants = problem.getConstantList();
    this.newVars = new Vector<AlgebraVariable>();
    this.newTerms = new Vector<AlgebraTerm>();

    /* new variables are v_number */
        FreshVarGenerator fvg = new FreshVarGenerator(W, FreshNameGenerator.TYPE_INFERENCE);

    String prefix = "v";
    Sort sort = problem.getSort();

    int newVarCount = homSol.size();
    for(int i = 0; i < newVarCount; i++) {
        this.newVars.add(fvg.getFreshVariable(prefix, sort, false));
    }

    /* add the new variables and constants */
    this.newTerms.addAll(this.newVars);
    this.newTerms.addAll(constants);

    /* L = number of constants */
    int L = intVec.size() - hom.size();

    if(L == 0) {
        /* no constants */
        this.unifierLists = new Vector();
        this.unifierLists.add(homSol);
        if(construct) {
            res.add(this.construct(homSol, this.oldVars, this.newTerms, this.f));
        }
    }
    else {
        /* get solutions to inhomogeneous equations */
        Vector collect = new Vector();
        Iterator i = constants.iterator();
        while(i.hasNext()) {
        AlgebraTerm tt = (AlgebraTerm)i.next();
        DioInhom dioinhom = DioInhom.create(hom, -problem.getConstantCount(tt));
        collect.add(dioinhom.specialSolutions());
        }

        /* cartesian product of these */
        Vector product = this.product((Vector)collect.clone());
        this.unifierLists = new Vector();

        i = product.iterator();
        while(i.hasNext()) {
        Vector v = (Vector)i.next();
        List<IntVector> l = new Vector<IntVector>(homSol);
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


    /* constructs a substitution from IntVectors */
    private AlgebraSubstitution construct(List<IntVector> sol, List<AlgebraVariable> oldVars, List<AlgebraTerm> newTerms, SyntacticFunctionSymbol f) {
    AlgebraSubstitution res = AlgebraSubstitution.create();

    Iterator i = oldVars.iterator();
    int ni = 0;

    /* for each "old" variable... */
    while(i.hasNext()) {
        /* ...construct a list of the arguments it is mapped to */
        AlgebraVariable v = (AlgebraVariable)i.next();
        List<AlgebraTerm> args = new Vector<AlgebraTerm>();
        Iterator j = sol.iterator();
        int nj = 0;
        while(j.hasNext()) {
        IntVector intVec = (IntVector)j.next();
        AlgebraTerm tt = newTerms.get(nj);
        for(int k=0; k<intVec.get(ni); k++) {
            args.add(tt);
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
    if(args.size()==0) {
        throw new RuntimeException("no unit in ACUWithConstants");
    }
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

    /* cartesian product of the lists in v */
    private Vector product(Vector v) {
    if(v.size()==1) {
        return this.vectorize(v);
    }

    Vector res = new Vector();
    Vector w = (Vector)v.get(0);
    v.removeElementAt(0);

    /* construct cartesian product of the remaining lists */
    Vector r = this.product(v);

    Iterator i = w.iterator();
    while(i.hasNext()) {
        Object o = i.next();
        Iterator j = r.iterator();
        while(j.hasNext()) {
        /* add o to all products of the rest */
        Vector rr = (Vector)j.next();
        Vector rrr = new Vector();
        rrr.add(o);
        rrr.addAll(rr);
        res.add(rrr);
        }
    }

    return res;
    }

    /* each element of v is put into a list of its own */
    private Vector vectorize(Vector v) {
    Vector res = new Vector();
    Vector w = (Vector)v.get(0);

    Iterator i = w.iterator();
    while(i.hasNext()) {
        Object o = i.next();
        Vector r = new Vector();
        r.add(o);
        res.add(r);
    }

    return res;
    }

    @Override
    public boolean areTheoryUnifiable(AlgebraTerm s, AlgebraTerm t) {
    /* ACU unify s and t */
    HashSet<AlgebraVariable> W = new HashSet<AlgebraVariable>(s.getVars());
    W.addAll(t.getVars());
    this.unify(s, t, W, false);

    return !this.getUnifierLists().isEmpty();
    }

}
