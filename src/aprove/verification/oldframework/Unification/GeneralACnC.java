package aprove.verification.oldframework.Unification;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Unification.Problems.*;
import aprove.verification.oldframework.Unification.Utility.*;

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

    private Set<SyntacticFunctionSymbol> acSig;
    private Set<SyntacticFunctionSymbol> cSig;

    public GeneralACnC(Set<SyntacticFunctionSymbol> acSig) {
    this.acSig = acSig;
    this.cSig = new LinkedHashSet<SyntacticFunctionSymbol>();
    }

    /** Creates a new GeneralACnC.
     * @param acSig the function symbols that are AC
     * @param cSig the function symbols that are C
     */
    public GeneralACnC(Set<SyntacticFunctionSymbol> acSig, Set<SyntacticFunctionSymbol> cSig) {
    this.acSig = acSig;
    this.cSig = cSig;
    }

    /** Returns the AC symbols.
     */
    @Override
    public Set<SyntacticFunctionSymbol> getACs() {
    return this.acSig;
    }

    /** Returns the C symbols.
     */
    public Set<SyntacticFunctionSymbol> getCs() {
    return this.cSig;
    }

    /** Returns a complete set of unifiers if s and t are
     * unifiable, returns an empty set otherwise.
     */
    @Override
    public Collection<AlgebraSubstitution> unify(AlgebraTerm s, AlgebraTerm t, Set<AlgebraVariable> W) {
    if(!s.getSymbol().equals(t.getSymbol()) && !s.isVariable() && !t.isVariable()) {
        return new Vector<AlgebraSubstitution>();
    }
    Set<AlgebraVariable> V = new HashSet<AlgebraVariable>(s.getVars());
    V.addAll(t.getVars());

    GeneralACnCProblem acp = GeneralACnCProblem.create(this.acSig, this.cSig, V, W);
    acp.add(s, t);

    Collection<AlgebraSubstitution> res = new HashSet<AlgebraSubstitution>();

    Stack problems = new Stack();
    problems.push(acp);

    while(!problems.isEmpty()) {
        GeneralACnCProblem prob = (GeneralACnCProblem)problems.pop();

        if(!prob.fail() && !prob.cycleCheck()) {
        boolean solved = true;
        boolean hasAC = false;
        /* AC probs */
        Iterator i = this.acSig.iterator();
        List<PairOfACnCTerms> subprob = null;
        SyntacticFunctionSymbol f = null;
        while(i.hasNext() && solved) {
            f = (SyntacticFunctionSymbol)i.next();
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
                f = (SyntacticFunctionSymbol)i.next();
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
            i = acprob.getQuasiSolvedForms().iterator();
            while(i.hasNext()) {
            GeneralACnCProblem probclone = prob.shallowcopy();
            List<PairOfACnCTerms> next;
            if(hasAC) {
                next = this.toACnCProb((List<PairOfACTerms>)i.next(), this.cSig);
            }
            else {
                next = (List<PairOfACnCTerms>)i.next();
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
    public boolean areTheoryUnifiable(AlgebraTerm s, AlgebraTerm t) {
    Set<AlgebraVariable> V = new HashSet<AlgebraVariable>(s.getVars());
    V.addAll(t.getVars());
    Set<AlgebraVariable> W = V;

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
        Iterator i = this.acSig.iterator();
        List<PairOfACnCTerms> subprob = null;
        SyntacticFunctionSymbol f = null;
        while(i.hasNext() && solved) {
            f = (SyntacticFunctionSymbol)i.next();
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
            f = (SyntacticFunctionSymbol)i.next();
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
                i = acprob.iterateQuasiSolvedForms();
                while(i.hasNext() && !res) {
                    GeneralACnCProblem probclone = prob.shallowcopy();
                    List<PairOfACnCTerms> next;
                    if(hasAC) {
                    next = this.toACnCProb((List<PairOfACTerms>)i.next(), this.cSig);
                    }
                    else {
                    next = (List<PairOfACnCTerms>)i.next();
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
    Iterator i = acnc.iterator();
    while(i.hasNext()) {
        res.add(((PairOfACnCTerms)i.next()).toPairOfACTerms());
    }
    return res;
    }

    private List<PairOfACnCTerms> toACnCProb(List<PairOfACTerms> ac, Set<SyntacticFunctionSymbol> cs) {
    List<PairOfACnCTerms> res = new Vector<PairOfACnCTerms>();
    Iterator i = ac.iterator();
    while(i.hasNext()) {
        res.add(((PairOfACTerms)i.next()).toPairOfACnCTerms(cs));
    }
    return res;
    }

}
