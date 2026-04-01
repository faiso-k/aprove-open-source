package aprove.verification.oldframework.Unification.Problems;

import java.util.*;

import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Unification.Utility.*;

/**
 *  Representation of an ACU unification problem with constants.
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class ACUWithConstantsProblem {

    private AlgebraTerm s;
    private AlgebraTerm t;
    private MultisetOfTerms sMul;
    private MultisetOfTerms tMul;
    private List<AlgebraTerm> termlist;
    private IntVector G1;
    private int varCount;
    private Sort sort;
    private SyntacticFunctionSymbol fun;
    private boolean trivial;

    private ACUWithConstantsProblem(AlgebraTerm s, AlgebraTerm t) {
    this.s = s;
    this.t = t;
    this.sort = s.getSymbol().getSort();
    this.fun = (SyntacticFunctionSymbol)s.getSymbol();
    this.sMul = MultisetOfTerms.createACU(s);
    this.tMul = MultisetOfTerms.createACU(t);
    this.termlist = this.constructTermList();
    this.trivial = this.termlist.isEmpty();
    this.G1 = this.constructIntVector();
    this.varCount = this.getVarCount();
    }

    private List<AlgebraTerm> constructTermList() {
    MultisetOfTerms restLeft = this.sMul.subtract(this.tMul);
    MultisetOfTerms restRight = this.tMul.subtract(this.sMul);

    SortedSet<AlgebraTerm> terms = new TreeSet<AlgebraTerm>(new TermComparator());
    Enumeration e = restLeft.elements();
    while(e.hasMoreElements()) {
        terms.add((AlgebraTerm)e.nextElement());
    }
    e = restRight.elements();
    while(e.hasMoreElements()) {
        terms.add((AlgebraTerm)e.nextElement());
    }

    return new Vector<AlgebraTerm>(terms);
    }

    private IntVector constructIntVector() {
    int[] tmp = new int[this.termlist.size()];

    Iterator i = this.termlist.iterator();
    int count = 0;
    while(i.hasNext()) {
        AlgebraTerm tt = (AlgebraTerm)i.next();
        tmp[count] = this.sMul.numberOfOccurences(tt) - this.tMul.numberOfOccurences(tt);
        count++;
    }

    return IntVector.create(tmp, 0);
    }

    private int getVarCount() {
    int res = 0;
    boolean hasVar = true;
    Iterator i = this.termlist.iterator();
    while(i.hasNext() && hasVar) {
        AlgebraTerm tt = (AlgebraTerm)i.next();
        if(tt.isVariable()) {
        res++;
        }
        else {
        hasVar = false;
        }
    }
    return res;
    }

    /** Creates a new ACUWithConstantsProblem. */
    public static ACUWithConstantsProblem create(AlgebraTerm s, AlgebraTerm t) {
    return new ACUWithConstantsProblem(s, t);
    }

    public boolean isTrivial() {
    return this.trivial;
    }

    /** Returns the list of terms of this ACUWithConstantsProblem.
     */
    public List<AlgebraTerm> getTermList() {
    return this.termlist;
    }

    /** Returns the list of variables of this ACUWithConstantsProblem.
     */
    public List<AlgebraVariable> getVariableList() {
    List<AlgebraVariable> res = new Vector<AlgebraVariable>();

    for(int i= 0; i<this.varCount; i++) {
        res.add((AlgebraVariable)this.termlist.get(i));
    }

    return res;
    }

    /** Returns the list of constants of this ACUWithConstantsProblem.
     */
    public List<AlgebraTerm> getConstantList() {
    List<AlgebraTerm> res = new Vector<AlgebraTerm>();

    for(int i= this.varCount; i<this.termlist.size(); i++) {
        res.add(this.termlist.get(i));
    }

    return res;
    }

    /** Returns the IntVector associated to this ACUWithConstantsProblem.
     */
    public IntVector getIntVector() {
    return this.G1;
    }

    /** Returns the part of the IntVector associated to this ACUWithConstantsProblem that
     * handels the variables.
     */
    public IntVector getHom() {
    int[] hom = new int[this.varCount];
    for(int i=0; i<this.varCount; i++) {
        hom[i] = this.G1.get(i);
    }
    return IntVector.create(hom, 0);
    }

    public int getConstantCount(AlgebraTerm tt) {
    return this.G1.get(this.termlist.indexOf(tt));
    }

    public Sort getSort() {
    return this.sort;
    }

    public SyntacticFunctionSymbol getFunctionSymbol() {
    return this.fun;
    }


    /* Comparator that places variables before constants and sorts like symbols according to their name */
    private class TermComparator implements Comparator {

    @Override
    public int compare(Object o1, Object o2) {
        AlgebraTerm s = (AlgebraTerm)o1;
        AlgebraTerm t = (AlgebraTerm)o2;

        if(s.isVariable()) {
        if(t.isVariable()) {
            return s.toString().compareTo(t.toString());
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
