package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Visitors.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

/**
 * @author dickmeis
 * @version $Id$
 */
@NoParams
public class InverseLASubstitutionProcessor extends TheoremProverProcessor {

    @Override
    protected Result process(TheoremProverObligation obligationInput, BasicObligationNode obligationNode, Abortion aborter,
                RuntimeInformation rti) throws AbortionException {
        // get formula to generalise
        Formula formula = obligationInput.getFormula();

        LAProgramProperties laProgram = obligationInput.getProgram().laProgramProperties;

        List<Pair<AlgebraTerm, Position>> res = LASubtermAndPositionGetter.apply(formula, laProgram);

        Comparator<Pair<AlgebraTerm, Position>> comp2nd = new Comparator<Pair<AlgebraTerm, Position>>(){
            @Override
            public int compare(Pair<AlgebraTerm, Position> o1, Pair<AlgebraTerm, Position> o2) {
                return o1.y.compareTo(o2.y) ;
            }
        };
        Collections.sort(res, comp2nd);

        // delete subpositions
        // after this only maximal LA terms are regarded
        for(int i = 0; i < res.size()-1; i++){
            Position pos1 = res.get(i).y;
            Position pos2 = res.get(i+1).y;
            boolean isSubPosition = pos2.isSubPosition(pos1);
            if (isSubPosition){
                res.remove(i+1);
                i--;
            }
        }

        // remove variable and ground terms
        for(int i = 0; i < res.size()-1; i++){
            Position pos = res.get(i).y;

            try {
                AlgebraTerm t = (AlgebraTerm) formula.getSubPart(pos);

                if (t instanceof AlgebraVariable) {
                    res.remove(i+1);
                    i--;
                }

                if (t.getVars().isEmpty()){
                    res.remove(i+1);
                    i--;
                }
            }
            catch (InvalidPositionException e) {
                res.remove(i+1);
                i--;
            }
        }

        if(res.size() < 2) {
            return ResultFactory.notApplicable();
        }

        List<List<Pair<AlgebraTerm, Position>>> candidates = new ArrayList<List<Pair<AlgebraTerm, Position>>> ();

        for(int i = 0; i < res.size() - 1; i++){
            Pair<AlgebraTerm, Position> p1 = res.get(i);

            List<Pair<AlgebraTerm, Position>> equivs = null;
            for(int j = i+1; j < res.size(); j++){
                Pair<AlgebraTerm, Position> p2 = res.get(j);

                LinearConstraint constraint = LinearConstraint.createEquation(p1.x, p2.x, laProgram);
                if(constraint.getConstant().equals(Rational.zero)
                        && constraint.getCoefficients().isEmpty()){
                    if(equivs==null){
                        equivs = new ArrayList<Pair<AlgebraTerm,Position>>();
                        equivs.add(p1);
                    }
                    equivs.add(p2);

                    res.remove(j);
                    j--;
                }
            }

            if(equivs!=null){
                candidates.add(equivs);
            }
        }

        if(candidates.isEmpty()) {
            return ResultFactory.notApplicable();
        }

        // compares size of all terms that will get replaced
        Comparator<List<Pair<AlgebraTerm, Position>>> comp = new Comparator<List<Pair<AlgebraTerm, Position>>>(){
            @Override
            public int compare(List<Pair<AlgebraTerm, Position>> o1, List<Pair<AlgebraTerm, Position>> o2) {
                int o1size = 0;
                for (Pair<AlgebraTerm, Position> p : o1) {
                    o1size += p.x.size();
                }

                int o2size = 0;
                for (Pair<AlgebraTerm, Position> p : o2) {
                    o2size += p.x.size();
                }

                return o2size - o1size;
            }
        };
        Collections.sort(candidates, comp);

        List<Pair<AlgebraTerm, Position>> bestCandidate = candidates.get(0);

        Formula newFormula = formula.deepcopy();

        //  get fresh variable
        Set<AlgebraVariable> usedVariables = obligationInput.getAllVariables();

        FreshVarGenerator fvg = new FreshVarGenerator(usedVariables);
        AlgebraVariable freshVar = fvg.getFreshVariable("n", laProgram.sortNat, false);

        for (Pair<AlgebraTerm, Position> pair : bestCandidate) {
            try {
                newFormula = newFormula.replaceTermAt(freshVar, pair.y);
            }
            catch (InvalidPositionException e) {
                e.printStackTrace();
                return ResultFactory.error(e);
            }
        }

        // create new obligation
        TheoremProverObligation newObligation = new TheoremProverObligation(newFormula, obligationInput);

        InverseLASubstitutionProof proof = new InverseLASubstitutionProof(newObligation, bestCandidate, freshVar);

        return ResultFactory.proved(newObligation, YNMImplication.SOUND, proof);

    }

}
