package aprove.verification.oldframework.Algebra.Matrices;

import java.util.*;

import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Algebra.Matrices.Interpretation.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Converts SimplePolyConstraints with QActiveConditions to Diophantine logic.
 *
 * @author Patrick Kabasci
 * @version $Id$
 */

public class DLActiveParser {

    public static Formula<Diophantine> convert( Map<QActiveCondition,Set<SimplePolyConstraint>> input, MatrixFactory fact, ArgumentInterpretor argInter) {

        ActiveResolver activeResolver = new ActiveResolver();
        activeResolver.setIsActive();

        FormulaFactory<Diophantine> ff = NonCountingCircuitFactory.create(SplitMode.FLATTEN, SplitMode.LEFT_COMB);

        List<SimplePolynomial> retForms = new ArrayList<SimplePolynomial>();
        List<Formula<Diophantine>> disjuncts = new ArrayList<Formula<Diophantine>>();
        List<Formula<Diophantine>> conjuncts = new ArrayList<Formula<Diophantine>>();
        List<Formula<Diophantine>> masterDisjuncts = new ArrayList<Formula<Diophantine>>();
        List<Formula<Diophantine>> masterConjuncts = new ArrayList<Formula<Diophantine>>();
        List<Formula<Diophantine>> currentConjuncts = new ArrayList<Formula<Diophantine>>();

        for (Map.Entry<QActiveCondition, Set<SimplePolyConstraint>> entry: input.entrySet()) {
            masterDisjuncts.clear();
            for (Set<Pair<FunctionSymbol,Integer>> curElem: entry.getKey().getSetRepresentation()) {
                conjuncts.clear();
                for (Pair<FunctionSymbol, Integer> pair: curElem) {
                    retForms.clear();
                    disjuncts.clear();
                    retForms.addAll(argInter.getFSymCoefficients(pair.x, pair.y, fact));
                    for (SimplePolynomial s: retForms){
                         disjuncts.add(ff.buildTheoryAtom(Diophantine.create( new SimplePolyConstraint(s, ConstraintType.GT))));
                    }
                    conjuncts.add(ff.buildOr(disjuncts));
                }
                masterDisjuncts.add(ff.buildAnd(conjuncts));
            }
            currentConjuncts.clear();
            for (SimplePolyConstraint cons: entry.getValue()) {
                currentConjuncts.add(ff.buildTheoryAtom(Diophantine.create(cons)));
            }
            masterConjuncts.add(ff.buildImplication(ff.buildOr(masterDisjuncts), ff.buildAnd(currentConjuncts)));
        }



        return ff.buildAnd(masterConjuncts);

    }




}

