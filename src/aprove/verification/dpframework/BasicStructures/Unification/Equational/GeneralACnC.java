/*
 * Created on Feb 17, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.Equational.Problems.*;
import aprove.verification.dpframework.BasicStructures.Unification.Equational.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 *  Unification algorithm for general AC-and-C unification.
 *  <p>
 *  This is basically an extension of the general AC unification algorithm of
 *  <br>
 *  A. Boudet: "Competing for the AC-Unification Race", JAR 11, pp. 185-212
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class GeneralACnC extends GeneralAC {

    private Set<FunctionSymbol> acSig;
    private Set<FunctionSymbol> cSig;

    public GeneralACnC(Set<FunctionSymbol> acSig) {
        this.acSig = acSig;
        this.cSig = new LinkedHashSet<FunctionSymbol>();
    }

    /** Creates a new GeneralACnC.
     * @param acSig the function symbols that are AC
     * @param cSig the function symbols that are C
     */
    public GeneralACnC(Set<FunctionSymbol> acSig, Set<FunctionSymbol> cSig) {
        this.acSig = acSig;
        this.cSig = cSig;
    }

    /** Returns the AC symbols.
     */
    @Override
    public Set<FunctionSymbol> getACs() {
        return this.acSig;
    }

    /** Returns the C symbols.
     */
    public Set<FunctionSymbol> getCs() {
        return this.cSig;
    }

    /** Returns a complete set of unifiers if s and t are
     * unifiable, returns an empty set otherwise.
     */
    @Override
    public Collection<TRSSubstitution> unify(TRSTerm s, TRSTerm t, Set<TRSVariable> W) {
        if(!s.isVariable() && !t.isVariable()
                && !((TRSFunctionApplication)s).getRootSymbol().equals(((TRSFunctionApplication)t).getRootSymbol()) ) {
            return new Vector<TRSSubstitution>();
        }
        Set<TRSVariable> V = new HashSet<TRSVariable>(s.getVariables());
        V.addAll(t.getVariables());

        GeneralACnCProblem acp = GeneralACnCProblem.create(this.acSig, this.cSig, V, W);
        acp.add(s, t);

        Collection<TRSSubstitution> res = new HashSet<TRSSubstitution>();

        Stack<GeneralACnCProblem> problems = new Stack<GeneralACnCProblem>();
        problems.push(acp);

        while(!problems.isEmpty()) {
            GeneralACnCProblem prob = (GeneralACnCProblem)problems.pop();

            if(!prob.fail() && !prob.cycleCheck()) {
                boolean solved = true;
                boolean hasAC = false;
                /* AC probs */
                Iterator<FunctionSymbol> i = this.acSig.iterator();
                List<PairOfACnCTerms> subprob = null;
                FunctionSymbol f = null;
                while(i.hasNext() && solved) {
                    f = i.next();
                    subprob = prob.getTransformed(f);
                    solved = solved && subprob.isEmpty();
                    if(!solved) {
                        hasAC = true;
                    }
                }

                if(solved) {
                    /* C probs */
                    i = this.cSig.iterator();
                    while(i.hasNext() && solved) {
                        f = i.next();
                        subprob = prob.getTransformed(f);
                        solved = solved && subprob.isEmpty();
                    }
                }

                if(solved) {
                    res.add(ElementaryUnification.baseAway(prob.toSubst(), V, W));
                }
                else {
                    /* handle subprob */
                    SystemOfElementaryProblems acprob;
                    if(hasAC) {
                        /* handle next AC subprob */
                        acprob = SystemOfElementaryACProblems.create(this.toACProb(subprob), f, prob.getAbsVars(), prob.getFreshVarGen(), this.acSig);
                    }
                    else {
                        /* handle next C subprob */
                        acprob = SystemOfElementaryCProblems.create(subprob, f);
                    }
                    Iterator it = acprob.getQuasiSolvedForms().iterator();
                    while(it.hasNext()) {
                        GeneralACnCProblem probclone = prob.shallowcopy();
                        List<PairOfACnCTerms> next;
                        if(hasAC) {
                            next = this.toACnCProb((List<PairOfACTerms>)it.next(), this.cSig);
                        }
                        else {
                            next = (List<PairOfACnCTerms>)it.next();
                        }
                        probclone.addAll(next);
                        problems.add(probclone);
                    }
                }
            }
        }

        return res;
    }

    @Override
    public boolean areTheoryUnifiable(TRSTerm s, TRSTerm t) {
        Set<TRSVariable> V = new HashSet<TRSVariable>(s.getVariables());
        V.addAll(t.getVariables());
        Set<TRSVariable> W = V;

        GeneralACnCProblem acp = GeneralACnCProblem.create(this.acSig, this.cSig, V, W);
        acp.add(s, t);

        return this.unifyHelper(acp);
    }

    private boolean unifyHelper(GeneralACnCProblem prob) {
        boolean res = false;
        if(!prob.fail() && !prob.cycleCheck()) {
            boolean solved = true;
            boolean hasAC = false;
            boolean hasC = false;
            Iterator<FunctionSymbol> i = this.acSig.iterator();
            List<PairOfACnCTerms> subprob = null;
            FunctionSymbol f = null;
            while(i.hasNext() && solved) {
                f = i.next();
                subprob = prob.getTransformed(f);
                solved = solved && subprob.isEmpty();
                if(!solved) {
                    hasAC = true;
                }
            }
            if(solved) {
                /* C probs */
                i = this.cSig.iterator();
                while(i.hasNext() && solved) {
                    f = (FunctionSymbol)i.next();
                    subprob = prob.getTransformed(f);
                    solved = solved && subprob.isEmpty();
                    if(!solved) {
                        hasC = true;
                    }
                }
            }
            if(solved) {
                res = true;
            }
            else {
                /* handle subprob */
                SystemOfElementaryACProblems acp = null;
                SystemOfElementaryProblems acprob;
                if(hasAC) {
                    acp = SystemOfElementaryACProblems.create(this.toACProb(subprob), f, prob.getAbsVars(), prob.getFreshVarGen(), this.acSig);
                    acprob = acp;
                }
                else {
                    acprob = SystemOfElementaryCProblems.create(subprob, f);
                }
                if (hasAC && acp.isTrivial()) {
                    res = this.unifyHelper(prob);
                } else {
                    Iterator it = acprob.iterateQuasiSolvedForms();
                    while(it.hasNext() && !res) {
                        GeneralACnCProblem probclone = prob.shallowcopy();
                        List<PairOfACnCTerms> next;
                        if(hasAC) {
                            next = this.toACnCProb((List<PairOfACTerms>)it.next(), this.cSig);
                        }
                        else {
                            next = (List<PairOfACnCTerms>)it.next();
                        }
                        probclone.addAll(next);
                        res = this.unifyHelper(probclone);
                    }
                }
            }
        }

        return res;
    }

    private List<PairOfACTerms> toACProb(List<PairOfACnCTerms> acnc) {
        List<PairOfACTerms> res = new Vector<PairOfACTerms>();
        for(PairOfACnCTerms p:acnc) {
            res.add(p.toPairOfACTerms());
        }
        return res;
    }

    private List<PairOfACnCTerms> toACnCProb(List<PairOfACTerms> ac, Set<FunctionSymbol> cs) {
        List<PairOfACnCTerms> res = new Vector<PairOfACnCTerms>();
        for(PairOfACTerms p:ac) {
            res.add(p.toPairOfACnCTerms(cs));
        }
        return res;
    }

}

