/*
 * Created on Feb 10, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational.Problems;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.Equational.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 *  Representation of an ACU unification problem with constants.
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class ACUWithConstantsProblem {

    private TRSTerm s;
    private TRSTerm t;
    private MultisetOfTerms sMul;
    private MultisetOfTerms tMul;
    private List<TRSTerm> termlist;
    private IntVector G1;
    private int varCount;
    private FunctionSymbol sSymbol; //RootSymbol of s iff s is a FunctionApplication else null
    private boolean trivial;

    private ACUWithConstantsProblem(TRSTerm s, TRSTerm t) {
        this.s = s;
        this.t = t;
        this.sSymbol = null;
        this.sMul = MultisetOfTerms.createACU(s);
        this.tMul = MultisetOfTerms.createACU(t);
        this.termlist = this.constructTermList();
        this.trivial = this.termlist.isEmpty();
        this.G1 = this.constructIntVector();
        this.varCount = this.getVarCount();
    }

    private List<TRSTerm> constructTermList() {
        MultisetOfTerms restLeft = this.sMul.subtract(this.tMul);
        MultisetOfTerms restRight = this.tMul.subtract(this.sMul);

        SortedSet<TRSTerm> terms = new TreeSet<TRSTerm>(new TermComparator());

        Enumeration<TRSTerm> e = restLeft.elements();
        while(e.hasMoreElements()) {
            terms.add(e.nextElement());
        }
        e = restRight.elements();
        while(e.hasMoreElements()) {
            terms.add((TRSTerm)e.nextElement());
        }

        return new Vector<TRSTerm>(terms);
    }

    private IntVector constructIntVector() {
        int[] tmp = new int[this.termlist.size()];

        int count = 0;
        for(TRSTerm tt : this.termlist) {
            tmp[count] = this.sMul.numberOfOccurences(tt) - this.tMul.numberOfOccurences(tt);
            count++;
        }

        return IntVector.create(tmp, 0);
    }

    private int getVarCount() {
        int res = 0;
        for(TRSTerm tt : this.termlist) {
            if(tt.isVariable()) {
                res++;
            }
            else {
                break;
            }
        }
        return res;
    }

    /** Creates a new ACUWithConstantsProblem. */
    public static ACUWithConstantsProblem create(TRSTerm s, TRSTerm t) {
        return new ACUWithConstantsProblem(s, t);
    }

    public boolean isTrivial() {
        return this.trivial;
    }

    /** Returns the list of terms of this ACUWithConstantsProblem.
     */
    public List<TRSTerm> getTermList() {
        return this.termlist;
    }

    /** Returns the list of variables of this ACUWithConstantsProblem.
     */
    public List<TRSVariable> getVariableList() {
        List<TRSVariable> res = new Vector<TRSVariable>();

        for(int i= 0; i<this.varCount; i++) {
            res.add((TRSVariable)this.termlist.get(i));
        }

        return res;
    }

    /** Returns the list of constants of this ACUWithConstantsProblem.
     */
    public List<TRSTerm> getConstantList() {
        List<TRSTerm> res = new Vector<TRSTerm>();

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

    public int getConstantCount(TRSTerm tt) {
        return this.G1.get(this.termlist.indexOf(tt));
    }

    public FunctionSymbol getFunctionSymbol() {
        if(this.s instanceof TRSFunctionApplication) {
            this.sSymbol = ((TRSFunctionApplication)this.s).getRootSymbol();
        }
        return this.sSymbol;
    }


    /** Comparator that places variables before constants and
     * functionapplications according to their name */
    private class TermComparator implements Comparator<TRSTerm> {

        @Override
        public int compare(TRSTerm s, TRSTerm t) {
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
