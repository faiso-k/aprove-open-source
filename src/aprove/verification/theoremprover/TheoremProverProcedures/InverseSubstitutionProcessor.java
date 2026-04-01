package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;
@NoParams
public class InverseSubstitutionProcessor extends TheoremProverProcessor {

    @Override
    protected Result process(TheoremProverObligation obligationInput, BasicObligationNode obligationNode, Abortion aborter,
                RuntimeInformation rti) throws AbortionException {
        // get formula to generalise
        Triple<Formula,AlgebraVariable,AlgebraTerm> result = InverseSubstitutionProcessor.inverseSubstitution(obligationInput);

        if(result==null) {
            return ResultFactory.notApplicable();
        }

        // create new obligation
        TheoremProverObligation newObligation = new TheoremProverObligation(result.x, obligationInput);
        return ResultFactory.proved(newObligation, YNMImplication.SOUND, new InverseSubstitutionProof(
                new Triple<TheoremProverObligation,AlgebraVariable,AlgebraTerm>(newObligation,result.y,result.z)));

    }

    public static Triple<Formula, AlgebraVariable, AlgebraTerm> inverseSubstitution(Formula formula, Set<AlgebraVariable> usedVariables) {

        TreeMap<ComparablePair<Integer,Integer>, List<AlgebraTerm>> candidates = new TreeMap<ComparablePair<Integer,Integer>,List<AlgebraTerm>>();

        // get all subterm with their positions of occurences
        Map<TermOrFormula,List<Position>> subParts = formula.getAllSubFormulasAndTermsWithPosition();

        for(Map.Entry<TermOrFormula,List<Position>> entry : subParts.entrySet()) {

            if(entry.getKey().isTerm()) {

                AlgebraTerm term = (AlgebraTerm)entry.getKey();

                // if term is a variable or a constant then try next candidate
                if(term.isVariable() || term.isConstant() ) { // || (term instanceof ConstructorApp)) {
                    continue;
                }

                // check if how many times the candidates occurs in the formula
                // if it is only once then it must be the guard of a if clause
                if( entry.getValue().size() == 1) {

                    // check sort of return value
                    if(term.getSort().getName().equals("bool")) {

                        // check if the term containing the candidate is
                        // a if-term
                        Position position = entry.getValue().get(0);
                        try {

                            // check if the subpart containing the candidate is a term
                            // otherwise continue
                            TermOrFormula subPart = formula.getSubPart(position.pred());
                            if(subPart.isTerm() && !position.isRootPosition()) {

                                // check if term is a if term
                                AlgebraTerm subPartAsTerm = (AlgebraTerm)subPart;
                                if((!subPartAsTerm.getSymbol().getName().startsWith("if_")) || (position.lastElement() != 0)) {
                                    continue;
                                }

                            }else {
                                continue;
                            }

                        }catch(InvalidPositionException e) {
                            throw new RuntimeException(e.getMessage());
                        }

                    }else{
                        continue;
                    }
                }

                ComparablePair<Integer,Integer> pair = new ComparablePair<Integer,Integer>(term.size(),entry.getValue().size());

                if(candidates.containsKey(pair)) {
                    candidates.get(pair).add(term);
                }else{
                    List<AlgebraTerm> candidateList = new Vector<AlgebraTerm>();
                    candidateList.add(term);
                    candidates.put(pair, candidateList);
                }

            }

        }

        if(candidates.isEmpty()) {
            return null;
        }

        AlgebraTerm bestCandidate = candidates.get(candidates.lastKey()).get(0);

        //  get fresh variable
        FreshVarGenerator fvg = new FreshVarGenerator(usedVariables);
        Sort sort = bestCandidate.getSort();
        AlgebraVariable freshVariable = fvg.getFreshVariable("n", sort, false);

        Formula newFormula = formula;
        for(Position position : subParts.get(bestCandidate)) {
            try {
                newFormula = newFormula.replaceTermAt(freshVariable, position);
            }catch(InvalidPositionException e){
                // could only happen due to a serious bug, so throw a runtime exception
                throw new RuntimeException(e.getMessage());
            }
        }

        return new Triple<Formula,AlgebraVariable,AlgebraTerm>(newFormula,freshVariable,bestCandidate);
    }

    public static Triple<Formula,AlgebraVariable,AlgebraTerm> inverseSubstitution(TheoremProverObligation obligationInput) {
        return InverseSubstitutionProcessor.inverseSubstitution(obligationInput.getFormula(), obligationInput.getAllVariables());
    }

}
