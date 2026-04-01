package aprove.verification.oldframework.Algebra.Terms;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.Visitors.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/**
 * A <code>TermBraid</code> is a occur failure in an unification problem.
 * i.e. term pairs are like these equations:<p>
 * <code> a = f(a), b = g(b,h(c)) </code><p>
 * Sometimes these braids have several similar forms:<p>
 * <code> a = g(f(h(a))), a = f(h(g(a))) </code>  or  <code> a = h(g(f(a))) </code> <p>
 * <code> b = f(g(b),h)</code> or <code> b=g(f(b,h)) </code> <p>
 * The goal is to convolve them to the prefered form.
 * @author Stephan Swiderski
 * @version $Id$
 */

public class TermBraid implements PairOfTerms {
    AlgebraFunctionApplication root;
    AlgebraVariable var;

    /**
     * compare two term braids by thier root symbols
     */
    public class TermBraidComparator implements Comparator{
        @Override
        public int compare(Object o1, Object o2) {
           Symbol sym1 = ((TermBraid) o1).getRoot().getFunctionSymbol();
       Symbol sym2 = ((TermBraid) o2).getRoot().getFunctionSymbol();
       return sym1.getName().compareTo(sym2.getName());
        }
    }

    /**
     * construct a TermBraid out of a occur failure pair
     * @param t1 one of these both terms has to be a variable
     * @param t2 and the other one has to be a function application
     */
    public TermBraid(AlgebraTerm t1,AlgebraTerm t2){
        if (t1 instanceof AlgebraVariable){ // swap in right form  f(a1,..,an)=ai --> ai = f(a1,...,an)
           this.var  = (AlgebraVariable) t1;
       this.root = (AlgebraFunctionApplication) t2;
    } else {
           this.var  = (AlgebraVariable) t2;
       this.root = (AlgebraFunctionApplication) t1;
    }
    }

    /**
     * get the left side i.e. the variable of this term braid
     * @return the variable of this termbraid
     */
    @Override
    public AlgebraTerm getLeft(){
        return this.var;
    }

    /**
     * get the left side i.e. the root of this term braid
     * @return the root of this term braid
     */
    @Override
    public AlgebraTerm getRight(){
        return this.root;
    }

    /**
     * get the left side i.e. the variable of this term braid
     * @return the variable of this term braid
     */
    public AlgebraVariable getVar(){
        return this.var;
    }

    /**
     * get the left side i.e. the root of this term braid
     * @return the root of this termbraid
     */
    public AlgebraFunctionApplication getRoot(){
        return this.root;
    }

    /**
     * get the first loop of this term braid.
     * ai = f(a1,...,an) result will be i
     * @return the looping position
     */
    public int getFirstLoop(){
        int i=0;
        Iterator it = (this.root.getArguments()).iterator();
    while (it.hasNext()){ // search the first occurence of variable var in the argumentlist
            AlgebraTerm argi = (AlgebraTerm)it.next(); // next argument
        if (argi.getVars().contains(this.var)){
            return i; // var occurs in argi
        }
        i++;
    }
        throw new RuntimeException("braid: this is no braid at all");
    }

    /**
     * unfold the term braid to basic equations: <p>
     * <code> a = f(g(a),h(i(a)) </code> <p>
     * <code> ==>  a = f(b,c), b = g(a), c = h(d), d = i(a) </code> <p>
     * @param generator some fresh Variables are needed
     * @return a set of pairs (equations) representing the term braid
     */
    private Set<PairOfTerms> unfold(FreshVarGenerator generator){
        Set<PairOfTerms> sopot = new HashSet<PairOfTerms>();
    AlgebraTerm repTerm = null;
    AlgebraTerm repVar = null;
    AlgebraTerm shTerm = null;
        int shLen = 32000;
    AlgebraTerm curTerm = null;
        int curLen = 32000;
    //System.out.println("w: "+ root.toString());
        Set<AlgebraTerm> sot = this.root.getFunctionSubterms();
    Iterator i = sot.iterator();
    while(i.hasNext()){
        curTerm = (AlgebraTerm) i.next();
            curLen = LengthVisitor.apply(curTerm);
        if (curLen < shLen) { shLen = curLen; shTerm = curTerm; }
    }
    while(sot.size()>1){
        repVar = generator.getFreshVariable("x", shTerm.getSymbol().getSort(), false);
        //repVar = tct.getFreshVariable();
        repTerm = shTerm;
        sot.remove(repTerm);
            sopot.add(new SimplePairOfTerms(repVar,repTerm));
        Set<AlgebraTerm> nsot = new LinkedHashSet<AlgebraTerm>();
        i = sot.iterator();
        shLen = 32000;
        while (i.hasNext()){
                curTerm = ((AlgebraTerm) i.next()).replaceTermByTerm(repTerm,repVar);
                nsot.add(curTerm);
            curLen = LengthVisitor.apply(curTerm);
        if (curLen < shLen) { shLen = curLen; shTerm = curTerm; }
        }
            sot = nsot;
    }
    sopot.add(new SimplePairOfTerms(this.var,shTerm));
/*
        Iterator it = sopot.iterator();
        while (it.hasNext()){
            SimplePairOfTerms pair = (SimplePairOfTerms)it.next();
            //System.out.println("meshs: "+ pair.toString());
    }
*/
    return sopot;
    }

    /**
     * build a term braid out of basic equations
     * but one basic equation is choosen to be the root.
     * <p>
     * braid: <code> a = g(f(h(a))) </code> <p>
     * basic equations: <code> a = g(b), b = f(c), c = h(a) </code> <p>
     * if <code>b = f(c)</code> is choosen to be the root
     * the resulting braid is: <code> b = f(h(g(b)) </code>.
     * Sometimes not all basic equations can play the role of the root
     * so then <code>null</code> is returned.
     * @param base basic equations which forms the root
     * @param meshSet the basic equations without the base
     * @return a term braid with base as the root, <code>null</code>
     * if base could not be root
     */
    private TermBraid buildTermBraid(PairOfTerms base,Set<PairOfTerms> meshSet){
        AlgebraSubstitution sub = AlgebraSubstitution.create();
        try{
           sub = AlgebraTerm.solveUP(meshSet,AlgebraSubstitution.create());
        } catch (UnificationException ue){
           return null;
        }
        return new TermBraid(base.getLeft(),base.getRight().apply(sub));
    }

    /**
     * term braids have sometimes several similar forms,
     * this method will generate all possible forms
     * @param generator some fresh variables are needed
     * @return all forms of this braid
     */
    public Set<TermBraid> getSimilarTermBraids(FreshVarGenerator generator){
        Set<PairOfTerms> meshSet = this.unfold(generator);
        Set<TermBraid> result = new HashSet<TermBraid>();
        Iterator i = meshSet.iterator();
        while (i.hasNext()){
            PairOfTerms  base = (PairOfTerms) i.next();
         Set<PairOfTerms> sopot = new HashSet<PairOfTerms>(meshSet);
        sopot.remove(base);
        TermBraid braid = this.buildTermBraid(base,sopot);
        if (braid != null) {
            result.add(braid);
            //System.out.println("braids: "+ braid.toString() );
        }
        }
        return result;
    }

    /**
     * select the braids with root function symbol with maximal arity
     * @param braidSet set to select from
     * @return a set with braids of maximal arity of their root function symbol
     */
    public Set<TermBraid> getMaxArityBraids(Set<TermBraid> braidSet){
        int arity = 0;
        Set<TermBraid> result = new HashSet<TermBraid>();
        Iterator i = braidSet.iterator();
        while (i.hasNext()){
            TermBraid braid = (TermBraid) i.next();
            int curArity = ((SyntacticFunctionSymbol) (braid.getRoot().getSymbol())).getArity();
        if (curArity > arity) { result.clear(); }
        if (curArity >= arity) { result.add(braid); arity = curArity; }
       }
       return result;
    }

    /**
     * select the shortest braids (term length)
     * @param braidSet set to select from
     * @return a set with shortest braids
     */
    public Set<TermBraid> getShortestBraids(Set<TermBraid> braidSet){
        int len = 32000;
        Set<TermBraid> result = new HashSet<TermBraid>();
        Iterator i = braidSet.iterator();
        while (i.hasNext()){
            TermBraid braid = (TermBraid) i.next();
            int curLen = LengthVisitor.apply(braid.getRoot());
        if (curLen < len) { result.clear(); }
        if (curLen <= len) { result.add(braid); len = curLen; }
       }
       return result;
    }

    /**
     * choose the first braid of a braidset ordered by the root symbols of the braids
     * @param braidSet to choose from
     * @return the choosen one
     */
    public TermBraid getFirstBraid(Set<TermBraid> braidSet){
        SortedSet<TermBraid> stb = new TreeSet<TermBraid>(new TermBraidComparator());
    stb.addAll(braidSet);
        return (TermBraid) stb.first();
    }

    /**
     * convolve the current braid to the maximal and shortest braid
     * out of the possible forms of this braid
     * @param generator some fresh variables needed
     */
    public void convolve(FreshVarGenerator generator){
        Set<TermBraid> braids = this.getSimilarTermBraids(generator);
        TermBraid tb = this.getFirstBraid(this.getShortestBraids(this.getMaxArityBraids(braids)));
        this.root = tb.getRoot();
        this.var = tb.getVar();
    }

    /*
     * @return a string representation of this object
     */
    @Override
    public String toString(){
        return this.var.toString() + "-=-" + this.root.toString();
    }
}
