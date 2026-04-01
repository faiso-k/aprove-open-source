/*
 * Created on Feb 14, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.Equational.Problems.*;
import aprove.verification.dpframework.BasicStructures.Unification.Equational.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 *  Unification algorithm for general AC unification.
 *  <p>
 *  A. Boudet: "Competing for the AC-Unification Race", JAR 11, pp. 185-212
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class GeneralAC extends GeneralUnification {

    private Set<FunctionSymbol> acSig;
    private ACWithConstants acwc;

    public GeneralAC() {
        this.acSig = new LinkedHashSet<FunctionSymbol>();
        this.acwc = new ACWithConstants();
    }

    /** Creates a new GeneralAC.
     * @param acSig the function symbols that are AC
     */
    public GeneralAC(Set<FunctionSymbol> acSig) {
        this.acSig = acSig;
        this.acwc = new ACWithConstants();
    }

    /** Returns the AC symbols.
     */
    public Set<FunctionSymbol> getACs() {
        return this.acSig;
    }

    /** Returns a set complete set of unifiers if s and t are
     * unifiable, returns an empty set otherwise.
     */
    @Override
    public Collection<TRSSubstitution> unify(TRSTerm s, TRSTerm t, Set<TRSVariable> W) {
        if(!s.isVariable() && !t.isVariable()
                && !((TRSFunctionApplication)s).getRootSymbol().equals(((TRSFunctionApplication)t).getRootSymbol()) ) {
            return new Vector<TRSSubstitution>();
        }
        if(this.isTotallyBoring(s, t)) {
            return this.acwc.unify(s, t, W);
        }

        Set<TRSVariable> V = new HashSet<TRSVariable>(s.getVariables());
        V.addAll(t.getVariables());

        GeneralACProblem acp = GeneralACProblem.create(this.acSig, V, W);
        acp.add(s, t);

        Collection<TRSSubstitution> res = new LinkedHashSet<TRSSubstitution>();

        Stack<GeneralACProblem> problems = new Stack<GeneralACProblem>();
        problems.push(acp);

        while(!problems.isEmpty()) {
            GeneralACProblem prob = problems.pop();

            if(!prob.fail() && !prob.cycleCheck()) {
                boolean solved = true;
                Iterator<FunctionSymbol> i = this.acSig.iterator();
                List<PairOfACTerms> subprob = null;
                FunctionSymbol f = null;
                while(i.hasNext() && solved) {
                    f = i.next();
                    subprob = prob.getTransformed(f);
                    solved = solved && subprob.isEmpty();
                }
                if(solved) {
                    res.add(ElementaryUnification.baseAway(prob.toSubst(), V, W));
                }
                else {
                    /* handle subprob */
                    SystemOfElementaryACProblems acprob = SystemOfElementaryACProblems.create(subprob, f, prob.getAbsVars(), prob.getFreshVarGen(), this.acSig);
                    for(List<PairOfACTerms> next:acprob.getQuasiSolvedForms()) {
                        GeneralACProblem probclone = prob.shallowcopy();
                        probclone.addAll(next);
                        problems.add(probclone);
                    }
                }
            }
        }

        return res;
    }


    private boolean isTotallyBoring(TRSTerm s, TRSTerm t) {
        ACTerm s_ = ACTerm.create(s, this.acSig);
        ACTerm t_ = ACTerm.create(t, this.acSig);
        return s instanceof TRSFunctionApplication && this.acSig.contains(((TRSFunctionApplication)s).getRootSymbol())
                && t instanceof TRSFunctionApplication && ((TRSFunctionApplication)s).getRootSymbol().equals(((TRSFunctionApplication)t).getRootSymbol())
                && s_.getAliens().isEmpty() && t_.getAliens().isEmpty();
    }

    @Override
    public boolean areTheoryUnifiable(TRSTerm s, TRSTerm t) {
        if(this.isTotallyBoring(s, t)) {
            return this.acwc.areTheoryUnifiable(s, t);
        }

        Set<TRSVariable> V = new HashSet<TRSVariable>(s.getVariables());
        V.addAll(t.getVariables());
        Set<TRSVariable> W = V;

        GeneralACProblem acp = GeneralACProblem.create(this.acSig, V, W);
        acp.add(s, t);

        return this.unifyHelper(acp);
    }

    private boolean unifyHelper(GeneralACProblem prob) {
        boolean res = false;
        if(!prob.fail() && !prob.cycleCheck()) {
            boolean solved = true;
            Iterator<FunctionSymbol> i = this.acSig.iterator();
            List<PairOfACTerms> subprob = null;
            FunctionSymbol f = null;
            while(i.hasNext() && solved) {
                f = i.next();
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
                    Iterator<List<PairOfACTerms>> it = acprob.iterateQuasiSolvedForms();
                    while(it.hasNext() && !res) {
                        GeneralACProblem probclone = prob.shallowcopy();
                        List<PairOfACTerms> next = it.next();
                        probclone.addAll(next);
                        res = this.unifyHelper(probclone);
                    }
                }
            }
        }

        return res;
    }

}
