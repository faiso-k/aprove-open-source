/*
 * Created on Feb 17, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational.Problems;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.Unification.Equational.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 *  Representation of a system of elementary C unification problems.
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class SystemOfElementaryCProblems implements SystemOfElementaryProblems {

    private List<PairOfACnCTerms> l;
    private FunctionSymbol f;

    private SystemOfElementaryCProblems(List<PairOfACnCTerms> l, FunctionSymbol f) {
        this.l = l;
        this.f = f;
        this.filter();
    }

    private void filter() {
        List<PairOfACnCTerms> newL = new Vector<PairOfACnCTerms>();
        for(PairOfACnCTerms p:this.l) {
            if(!p.isTrivial()) {
                newL.add(p);
            }
        }
        this.l = newL;
    }

    /** Creates a new SystemOfElementaryCProblems. */
    public static SystemOfElementaryCProblems create(List<PairOfACnCTerms> l, FunctionSymbol f) {
        return new SystemOfElementaryCProblems(l, f);
    }

    @Override
    public List<Vector<PairOfACnCTerms>> getQuasiSolvedForms() {
        List<Vector<PairOfACnCTerms>> res = new Vector<Vector<PairOfACnCTerms>>();
        int n = this.l.size();
        if(n==0) {
            /* trivial */
            res.add(new Vector<PairOfACnCTerms>());
            return res;
        }
        for (Sequence theSeq : SequenceGenerator.create(n, 2)) {
            List<PairOfACnCTerms> sol = new Vector<PairOfACnCTerms>();
            int j=0;
            for(PairOfACnCTerms p:this.l) {
                ACnCTerm left = p.getLeft();
                ACnCTerm right = p.getRight();
                List<ACnCTerm> largs = left.getArgVec();
                ACnCTerm l0;
                ACnCTerm l1;
                if(theSeq.get(j)==1) {
                    l0 = largs.get(1);
                    l1 = largs.get(0);
                }
                else {
                    l0 = largs.get(0);
                    l1 = largs.get(1);
                }
                List<ACnCTerm> rargs = right.getArgVec();
                sol.add(PairOfACnCTerms.create(l0, rargs.get(0)));
                sol.add(PairOfACnCTerms.create(l1, rargs.get(1)));
                j++;
            }
            res.add((Vector)sol);
        }
        return res;
    }


// iterator stuff

    @Override
    public Iterator iterateQuasiSolvedForms() {
        return new solIterator(this.l);
    }

    private class solIterator implements Iterator {

        private List<PairOfACnCTerms> l;
        private boolean hasNext;
        private int n;
        private boolean trivial;
        private List<PairOfACnCTerms> next;
        private Iterator<Sequence> seq;

        public solIterator(List<PairOfACnCTerms> l) {
            this.l = l;
            this.n = l.size();
            this.trivial = (this.n==0);
            this.hasNext = true;
            this.setup();
        }

        private void setup() {
            if(this.trivial) {
                this.next = new Vector<PairOfACnCTerms>();
            }
            else {
                this.seq = SequenceGenerator.create(this.n, 2).iterator();
                this.next = this.construct(this.seq.next());
            }
        }

        private List<PairOfACnCTerms> construct(Sequence s) {
            List<PairOfACnCTerms> sol = new Vector<PairOfACnCTerms>();
            int j=0;
            for(PairOfACnCTerms p:this.l) {
                ACnCTerm left = p.getLeft();
                ACnCTerm right = p.getRight();
                List<ACnCTerm> largs = left.getArgVec();
                ACnCTerm l0;
                ACnCTerm l1;
                if(s.get(j)==1) {
                    l0 = largs.get(1);
                    l1 = largs.get(0);
                }
                else {
                    l0 = largs.get(0);
                    l1 = largs.get(1);
                }
                List<ACnCTerm> rargs = right.getArgVec();
                sol.add(PairOfACnCTerms.create(l0, rargs.get(0)));
                sol.add(PairOfACnCTerms.create(l1, rargs.get(1)));
                j++;
            }
            return sol;
        }

        @Override
        public boolean hasNext() {
            return this.hasNext;
        }

        @Override
        public Object next() {
            List<PairOfACnCTerms> res = this.next;
            if(this.trivial || !this.seq.hasNext()) {
                this.hasNext = false;
                this.next = null;
            }
            else {
                this.next = this.construct(this.seq.next());
            }
            return res;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException("");
        }

    }

}

