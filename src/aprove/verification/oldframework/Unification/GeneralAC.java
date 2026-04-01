package aprove.verification.oldframework.Unification;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Unification.Problems.*;
import aprove.verification.oldframework.Unification.Utility.*;

/**
 *  Unification algorithm for general AC unification.
 *  <p>
 *  A. Boudet: "Competing for the AC-Unification Race", JAR 11, pp. 185-212
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class GeneralAC extends GeneralUnification {

    private Set<SyntacticFunctionSymbol> acSig;
    private ACWithConstants acwc;

    public GeneralAC() {
    this.acSig = new LinkedHashSet<SyntacticFunctionSymbol>();
    this.acwc = new ACWithConstants();
    }

    /** Creates a new GeneralAC.
     * @param acSig the function symbols that are AC
     */
    public GeneralAC(Set<SyntacticFunctionSymbol> acSig) {
    this.acSig = acSig;
    this.acwc = new ACWithConstants();
    }

    /** Returns the AC symbols.
     */
    public Set<SyntacticFunctionSymbol> getACs() {
    return this.acSig;
    }

    /** Returns a set complete set of unifiers if s and t are
     * unifiable, returns an empty set otherwise.
     */
    @Override
    public Collection<AlgebraSubstitution> unify(AlgebraTerm s, AlgebraTerm t, Set<AlgebraVariable> W) {
    if(!s.getSymbol().equals(t.getSymbol()) && !s.isVariable() && !t.isVariable()) {
        return new Vector<AlgebraSubstitution>();
    }
    if(this.isTotallyBoring(s, t)) {
        return this.acwc.unify(s, t, W);
    }

    Set<AlgebraVariable> V = new HashSet<AlgebraVariable>(s.getVars());
    V.addAll(t.getVars());

    GeneralACProblem acp = GeneralACProblem.create(this.acSig, V, W);
    acp.add(s, t);

    Collection<AlgebraSubstitution> res = new LinkedHashSet<AlgebraSubstitution>();

    Stack problems = new Stack();
    problems.push(acp);

    while(!problems.isEmpty()) {
        GeneralACProblem prob = (GeneralACProblem)problems.pop();

        if(!prob.fail() && !prob.cycleCheck()) {
        boolean solved = true;
        Iterator i = this.acSig.iterator();
        List<PairOfACTerms> subprob = null;
        SyntacticFunctionSymbol f = null;
        while(i.hasNext() && solved) {
            f = (SyntacticFunctionSymbol)i.next();
            subprob = prob.getTransformed(f);
            solved = solved && subprob.isEmpty();
        }
        if(solved) {
            res.add(ElementaryUnification.baseAway(prob.toSubst(), V, W));
        }
        else {
            /* handle subprob */
            SystemOfElementaryACProblems acprob = SystemOfElementaryACProblems.create(subprob, f, prob.getAbsVars(), prob.getFreshVarGen(), this.acSig);
            i = acprob.getQuasiSolvedForms().iterator();
            while(i.hasNext()) {
            GeneralACProblem probclone = prob.shallowcopy();
            List<PairOfACTerms> next = (List<PairOfACTerms>)i.next();
            probclone.addAll(next);
            problems.add(probclone);
            }
        }
        }
    }

    return res;
    }


    private boolean isTotallyBoring(AlgebraTerm s, AlgebraTerm t) {
    ACTerm s_ = ACTerm.create(s, this.acSig);
    ACTerm t_ = ACTerm.create(t, this.acSig);
    return this.acSig.contains(s.getSymbol()) && s.getSymbol().equals(t.getSymbol()) && s_.getAliens().isEmpty() && t_.getAliens().isEmpty();
    }

    @Override
    public boolean areTheoryUnifiable(AlgebraTerm s, AlgebraTerm t) {
    if(this.isTotallyBoring(s, t)) {
        return this.acwc.areTheoryUnifiable(s, t);
    }

    Set<AlgebraVariable> V = new HashSet<AlgebraVariable>(s.getVars());
    V.addAll(t.getVars());
    Set<AlgebraVariable> W = V;

    GeneralACProblem acp = GeneralACProblem.create(this.acSig, V, W);
    acp.add(s, t);

    return this.unifyHelper(acp);
    }

    private boolean unifyHelper(GeneralACProblem prob) {
    boolean res = false;
    if(!prob.fail() && !prob.cycleCheck()) {
        boolean solved = true;
        Iterator i = this.acSig.iterator();
        List<PairOfACTerms> subprob = null;
        SyntacticFunctionSymbol f = null;
        while(i.hasNext() && solved) {
            f = (SyntacticFunctionSymbol)i.next();
        subprob = prob.getTransformed(f);
        solved = solved && subprob.isEmpty();
        }
        if(solved) {
        res = true;
        }
        else {
            /* handle subprob */
            SystemOfElementaryACProblems acprob = SystemOfElementaryACProblems.create(subprob, f, prob.getAbsVars(), prob.getFreshVarGen(), this.acSig);
            if (acprob.isTrivial()) {
                res = this.unifyHelper(prob);
            } else {
                i = acprob.iterateQuasiSolvedForms();
                while(i.hasNext() && !res) {
                    GeneralACProblem probclone = prob.shallowcopy();
                    List<PairOfACTerms> next = (List<PairOfACTerms>)i.next();
                    probclone.addAll(next);
                    res = this.unifyHelper(probclone);
                }
            }
        }
    }

    return res;
    }

}
