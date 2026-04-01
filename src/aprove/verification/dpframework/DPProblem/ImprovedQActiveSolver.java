package aprove.verification.dpframework.DPProblem;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.QApplicativeUsableRules.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public interface ImprovedQActiveSolver extends QActiveSolver {

    /**
     * Tries to solve the constraints arising from the reduction pair processor.
     * @param P the set of pairs to orient (strict or non-strict, depending on allstrict)
     * @param R the set of rules to orient provided that the corresponding variables are true
     * @param sidecondition a formula that has to be satisfied and where one has to link the AfsProp-statements
     *                       to the encoded formula. I.e, the AfsProp f/i should be true iff the encoded order
     *                       regards the i-th argument of an f-term.
     * @param allstrict make all pairs in P strict (if true) or make at least one pair in P strict (if false)
     * @return null, if no solution is found. The order and the set of variables that are assigned TRUE (one only
     *          has to include those variables that are mentioned in R)
     */
    public Pair<? extends ExportableOrder<TRSTerm>, Set<Variable<AfsProp>>> solve(Set<Pair<TRSTerm, TRSTerm>> P, Collection<Pair<? extends GeneralizedRule,Variable<AfsProp>>> R, Formula<AfsProp> sidecondition, boolean allstrict, Abortion aborter) throws AbortionException;
    public boolean improvedSolvingSupported();

}
