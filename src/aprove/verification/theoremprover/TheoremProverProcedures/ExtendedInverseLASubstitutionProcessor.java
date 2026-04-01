package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.LinearArithmetic.*;
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
public class ExtendedInverseLASubstitutionProcessor extends TheoremProverProcessor {

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

        //  get fresh variable
        Set<AlgebraVariable> usedVariables = obligationInput.getAllVariables();

        FreshVarGenerator fvg = new FreshVarGenerator(usedVariables);
        AlgebraVariable freshVar = fvg.getFreshVariable("n", laProgram.sortNat, false);

        List<List<Triple<Position, AlgebraTerm, Integer>>> candidates = new ArrayList<List<Triple<Position, AlgebraTerm, Integer>>> ();

        for(int i = 0; i < res.size(); i++){
            Pair<AlgebraTerm, Position> p1 = res.get(i);

            AlgebraTerm q = p1.x;
            int qsize = q.size();

            List<Triple<Position, AlgebraTerm, Integer>> replacementWithSizes = new ArrayList<Triple<Position, AlgebraTerm, Integer>>();

            Triple<Position, AlgebraTerm, Integer> p = new Triple<Position, AlgebraTerm, Integer>(p1.y, freshVar, qsize);
            replacementWithSizes.add(p);

            for(int j = 0; j < res.size(); j++){
                if(i==j){
                    continue;
                }

                Pair<AlgebraTerm, Position> p2 = res.get(j);

                int k = 0;

                AlgebraTerm t_prime = p2.x;

                int tsize = t_prime.size();


                while(true){
                    // the condition is a bit more complicated
                    // we break on our own

                    AlgebraTerm[] greaterArgs = {q, t_prime};
                    AlgebraFunctionApplication lhs = AlgebraFunctionApplication.create(laProgram.fsLesseq, greaterArgs);
                    ConstructorApp rhs = ConstructorApp.create(laProgram.csTrue);
                    Equation loop_condition = Equation.create(lhs, rhs);

                    LinearConstraint loop_conditionConstraint = LinearConstraint.create(loop_condition, laProgram);

                    LASolver las = new LASolver();
                    las.addConstraint(loop_conditionConstraint);

                    boolean do_loop = las.solve();

                    if(do_loop){
                        t_prime = this.termSubtract(t_prime, q, laProgram);

                        k++;
                    }
                    else{
                        break;
                    }
                }

                if(k > 0){
                    AlgebraTerm t = freshVar;

                    int coeff = k - 1;

                    while(coeff > 0){
                        AlgebraTerm[] args = {t, freshVar};
                        t = AlgebraFunctionApplication.create(laProgram.fsPlus, args);
                        coeff--;
                    }

                    if( ! t_prime.equals(ConstructorApp.create(laProgram.csZero))){
                        AlgebraTerm[] args = {t, t_prime};
                        t = AlgebraFunctionApplication.create(laProgram.fsPlus, args);
                    }

                    Triple<Position, AlgebraTerm,Integer> repl = new Triple<Position, AlgebraTerm, Integer>(p2.y, t, tsize);
                    replacementWithSizes.add(repl);
                }

            }

            if(replacementWithSizes.size() > 1){
                candidates.add(replacementWithSizes);
            }
        }

        if(candidates.isEmpty()) {
            return ResultFactory.notApplicable();
        }

        // compares size of all terms that will get replaced
        Comparator<List<Triple<Position, AlgebraTerm,Integer>>> compReplSizes =
            new Comparator<List<Triple<Position, AlgebraTerm,Integer>>>(){

            @Override
            public int compare(List<Triple<Position, AlgebraTerm,Integer>> o1, List<Triple<Position, AlgebraTerm,Integer>> o2) {

                int o1size = 0;
                for (Triple<Position, AlgebraTerm,Integer> p : o1) {
                    o1size += p.z;
                }

                int o2size = 0;
                for (Triple<Position, AlgebraTerm,Integer> p : o2) {
                    o2size += p.z;
                }

                return o2size - o1size;
            }
        };
        Collections.sort(candidates, compReplSizes);

        List<Triple<Position, AlgebraTerm, Integer>> bestCandidate = candidates.get(0);

        Formula newFormula = formula.deepcopy();


        List<Triple<Position, AlgebraTerm, AlgebraTerm>> proofInformation =
            new ArrayList<Triple<Position,AlgebraTerm,AlgebraTerm>>(bestCandidate.size());

        for (Triple<Position, AlgebraTerm, Integer> triple : bestCandidate) {
            try {
                AlgebraTerm oldTerm = (AlgebraTerm) formula.getSubPart(triple.x);

                newFormula = newFormula.replaceTermAt(triple.y, triple.x);

                Triple<Position, AlgebraTerm, AlgebraTerm> proofInfo =
                    new Triple<Position, AlgebraTerm, AlgebraTerm>(triple.x, oldTerm, triple.y);

                proofInformation.add(proofInfo);
            }
            catch (InvalidPositionException e) {
                e.printStackTrace();
                return ResultFactory.error(e);
            }
        }

        // create new obligation
        TheoremProverObligation newObligation = new TheoremProverObligation(newFormula, obligationInput);

        ExtendedInverseLASubstitutionProof proof =
            new ExtendedInverseLASubstitutionProof(newObligation, proofInformation, freshVar);

        return ResultFactory.proved(newObligation, YNMImplication.SOUND, proof);

    }

    private AlgebraTerm termSubtract(AlgebraTerm t_prime, AlgebraTerm q, LAProgramProperties laProgram) {
        LinearTermNormalizer ltn = new LinearTermNormalizer(laProgram);

        t_prime.apply(ltn);

        Map<AlgebraVariable, Integer> t_coef = ltn.getCoefficients();
        int t_constant = -ltn.getConstant();

        ltn = new LinearTermNormalizer(laProgram);

        q.apply(ltn);

        Map<AlgebraVariable, Integer> q_coef = ltn.getCoefficients();
        int q_constant = -ltn.getConstant();

        HashMap<AlgebraVariable, Rational> dif_coef = new HashMap<AlgebraVariable, Rational>(t_coef.size());

        for (Entry<AlgebraVariable, Integer> entry: t_coef.entrySet()) {
            AlgebraVariable var = entry.getKey();

            int t_var_coef = entry.getValue();

            int q_var_coef = q_coef.get(var);

            int dif_var_coef = t_var_coef - q_var_coef;
            if(dif_var_coef != 0){
                dif_coef.put(var, new Rational(dif_var_coef));
            }
        }

        int dif_constant = t_constant - q_constant;

        AlgebraTerm t_new = LinearIntegerHelper.toTerm(dif_coef, new Rational(dif_constant), laProgram);

        return t_new;
    }

}
