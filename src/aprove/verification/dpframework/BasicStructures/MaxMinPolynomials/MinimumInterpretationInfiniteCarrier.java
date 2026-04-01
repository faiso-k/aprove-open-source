package aprove.verification.dpframework.BasicStructures.MaxMinPolynomials;


import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import immutables.*;

/**
 * Minimum Interpretation of 2 MaxMinPolynomials over the infinite carrier natural numbers
 *
 * @author Patrick Wiehe
 * @version $Id$
 */

public class MinimumInterpretationInfiniteCarrier implements InterpretLabelling{
    private InterpretLabelling interpret1;
    private InterpretLabelling interpret2;
    private final static MaxMinPolynomial ZERO = MaxMinPolynomial.getZERO();

    public MinimumInterpretationInfiniteCarrier(InterpretLabelling interpretation1, InterpretLabelling interpretation2) {
        this.interpret1 = interpretation1;
        this.interpret2 = interpretation2;
    }

    @Override
    public MaxMinPolynomial interpret(MaxMinPolynomial mmp1, MaxMinPolynomial mmp2) {
        MaxMinPolynomial argumentValue1 = this.interpret1.interpret(mmp1, mmp2);
        MaxMinPolynomial argumentValue2 = this.interpret2.interpret(mmp1, mmp2);
        if(argumentValue1.equals(MinimumInterpretationInfiniteCarrier.ZERO)) {
            return argumentValue1;
        }
        if(argumentValue2.equals(MinimumInterpretationInfiniteCarrier.ZERO)) {
            return argumentValue2;
        }
        if(argumentValue1.equals(argumentValue2)) {
            return argumentValue1;
        }
        else {
            Set<Set<VarPolynomial>> dominatedMinSets = new HashSet<Set<VarPolynomial>>();
            LinkedHashSet<ImmutableMap<String, ImmutableList<VarPolynomial>>> dominatedMinMapsMMP1 =
                new LinkedHashSet<ImmutableMap<String,ImmutableList<VarPolynomial>>>();
            LinkedHashSet<ImmutableMap<String, ImmutableList<VarPolynomial>>> dominatedMinMapsMMP2 =
                new LinkedHashSet<ImmutableMap<String,ImmutableList<VarPolynomial>>>();
            LinkedList<ImmutableMap<String, ImmutableList<VarPolynomial>>> mmp1VarMappingList
                =    new LinkedList<ImmutableMap<String, ImmutableList<VarPolynomial>>>(mmp1.getVariableMapping());
            LinkedList<ImmutableMap<String, ImmutableList<VarPolynomial>>> mmp2VarMappingList
                =    new LinkedList<ImmutableMap<String, ImmutableList<VarPolynomial>>>(mmp2.getVariableMapping());
            int positionMMP1List = 0;
            int positionMMP2List = 0;

            for( ; positionMMP1List < mmp1VarMappingList.size(); positionMMP1List++ ) {
                for ( ; positionMMP2List < mmp2VarMappingList.size(); positionMMP2List++ ) {
                    ImmutableMap<String, ImmutableList<VarPolynomial>> actbigMap = mmp2VarMappingList.get(positionMMP2List);
                    ImmutableMap<String, ImmutableList<VarPolynomial>> actsmallMap = mmp1VarMappingList.get(positionMMP1List);
                    boolean domination = MaxMinPolynomial.minTermDomination(actsmallMap, actbigMap);
                    if(domination) {
                        if(actsmallMap.equals(actbigMap)) {
                            mmp1VarMappingList.remove(positionMMP1List);
                            positionMMP1List--;
                            mmp2VarMappingList.remove(positionMMP2List);
                            dominatedMinMapsMMP1.add(actsmallMap);
                        }
                        else {
                            mmp2VarMappingList.remove(positionMMP2List);
                            dominatedMinMapsMMP1.add(actsmallMap);
                        }
                        break;
                    }
                    else {
                        //Check the other way round:
                        domination = MaxMinPolynomial.minTermDomination(actbigMap, actsmallMap);
                        if(domination) {
                            mmp2VarMappingList.remove(positionMMP2List);
                            dominatedMinMapsMMP2.add(actbigMap);
                            break;
                        }
                    }
                }
            }
            LinkedHashSet<LinkedHashSet<VarPolynomial>> reducedMMP1 = new LinkedHashSet<LinkedHashSet<VarPolynomial>>();
            LinkedHashSet<LinkedHashSet<VarPolynomial>> reducedMMP2 = new LinkedHashSet<LinkedHashSet<VarPolynomial>>();
            for( ImmutableMap<String, ImmutableList<VarPolynomial>> minSetMap : mmp1VarMappingList) {
                LinkedHashSet<ImmutableList<VarPolynomial>> containerSet = new LinkedHashSet<ImmutableList<VarPolynomial>>(minSetMap.values());
                LinkedHashSet<VarPolynomial> dummySet = new LinkedHashSet<VarPolynomial>();
                for(ImmutableList<VarPolynomial> vpList : containerSet) {
                    dummySet.addAll(vpList);
                }
                reducedMMP1.add(dummySet);
            }
            for( ImmutableMap<String, ImmutableList<VarPolynomial>> minSetMap : dominatedMinMapsMMP1) {
                LinkedHashSet<ImmutableList<VarPolynomial>> containerSet = new LinkedHashSet<ImmutableList<VarPolynomial>>(minSetMap.values());
                Set<VarPolynomial> dummySet = new HashSet<VarPolynomial>();
                for(ImmutableList<VarPolynomial> vpList : containerSet) {
                    dummySet.addAll(vpList);
                }
                dominatedMinSets.add(dummySet);
            }
            for( ImmutableMap<String, ImmutableList<VarPolynomial>> minSetMap : mmp2VarMappingList) {
                LinkedHashSet<ImmutableList<VarPolynomial>> containerSet = new LinkedHashSet<ImmutableList<VarPolynomial>>(minSetMap.values());
                LinkedHashSet<VarPolynomial> dummySet = new LinkedHashSet<VarPolynomial>();
                for(ImmutableList<VarPolynomial> vpList : containerSet) {
                    dummySet.addAll(vpList);
                }
                reducedMMP2.add(dummySet);
            }
            for( ImmutableMap<String, ImmutableList<VarPolynomial>> minSetMap : dominatedMinMapsMMP2) {
                LinkedHashSet<ImmutableList<VarPolynomial>> containerSet = new LinkedHashSet<ImmutableList<VarPolynomial>>(minSetMap.values());
                Set<VarPolynomial> dummySet = new HashSet<VarPolynomial>();
                for(ImmutableList<VarPolynomial> vpList : containerSet) {
                    dummySet.addAll(vpList);
                }
                dominatedMinSets.add(dummySet);
            }
            return this.varPolyDomination(reducedMMP1, reducedMMP2, dominatedMinSets);
        }
    }

    private MaxMinPolynomial varPolyDomination (
            LinkedHashSet<LinkedHashSet<VarPolynomial>> reducedMMP1,
            LinkedHashSet<LinkedHashSet<VarPolynomial>> reducedMMP2,
            Set<Set<VarPolynomial>> dominatedMinSets)
    {
        //Slightly less overhead, but loss of order :-)
        //Set<Set<VarPolynomial>> resultPoly = new HashSet<Set<VarPolynomial>>(dominatedMinSets);

        //Slightly more overhead, but it keeps the order of the VarPoly's
        //Easier for debugging.
        LinkedHashSet<LinkedHashSet<VarPolynomial>> resultPoly = new LinkedHashSet<LinkedHashSet<VarPolynomial>>();
        for(Set<VarPolynomial> dummySet : dominatedMinSets) {
            LinkedHashSet<VarPolynomial> dummy = new LinkedHashSet<VarPolynomial>(dummySet);
            resultPoly.add(dummy);
        }
        boolean insertFlag = true;
        for(LinkedHashSet<VarPolynomial> minsArg1 : reducedMMP1){
            for(LinkedHashSet<VarPolynomial> minsArg2 : reducedMMP2){

                //Set<VarPolynomial> resultMinPoly = new HashSet<VarPolynomial>(minsArg1); //to collect union of VarPoly of minsArg1 and minsArg2
                LinkedHashSet<VarPolynomial> resultMinPoly = new LinkedHashSet<VarPolynomial>(minsArg1);
                for(VarPolynomial candidatToAdd : minsArg2) {
                    Iterator<VarPolynomial> resultMinPolyIterator = resultMinPoly.iterator();
                    insertFlag = true;
                    while(resultMinPolyIterator.hasNext()) {
                        VarPolynomial actElem = resultMinPolyIterator.next();
                        VarPolynomial difference = actElem.minus(candidatToAdd);
                        if(difference.allPositive()) {
                            resultMinPolyIterator.remove();
                        }
                        else {
                            if(difference.allNegative()) {
                                insertFlag = false;
                            }
                        }
                    }
                    if(insertFlag) {
                        resultMinPoly.add(candidatToAdd);
                    }
                }
                resultPoly.add(resultMinPoly);
            }
        }
        return MaxMinPolynomial.create(resultPoly);
    }

    public MaxMinPolynomial interpret2(MaxMinPolynomial mmp1, MaxMinPolynomial mmp2) {
        MaxMinPolynomial argumentValue1 = this.interpret1.interpret(mmp1, mmp2);
        MaxMinPolynomial argumentValue2 = this.interpret2.interpret(mmp1, mmp2);

        if(argumentValue1.equals(MinimumInterpretationInfiniteCarrier.ZERO)) {
            return argumentValue1;
        }
        if(argumentValue2.equals(MinimumInterpretationInfiniteCarrier.ZERO)) {
            return argumentValue2;
        }
        if(argumentValue1.equals(argumentValue2)) {
            return argumentValue1;
        }
        else {
            LinkedHashSet<Set<VarPolynomial>> resultPoly = new LinkedHashSet<Set<VarPolynomial>>();//to collect the Set of Sets
            boolean insertFlag = true;
            for(ImmutableSet<VarPolynomial> minsArg1 : argumentValue1.getAllMinSets()){
                for(ImmutableSet<VarPolynomial> minsArg2 : argumentValue2.getAllMinSets()){
                 LinkedHashSet<VarPolynomial> resultMinPoly = new LinkedHashSet<VarPolynomial>(minsArg1); //to collect union of VarPoly of minsArg1 and minsArg2
                 for(VarPolynomial candidatToAdd : minsArg2) {
                     Iterator<VarPolynomial> resultMinPolyIterator = resultMinPoly.iterator();
                     insertFlag = true;
                     while(resultMinPolyIterator.hasNext()) {
                         VarPolynomial actElem = resultMinPolyIterator.next();
                         VarPolynomial difference = actElem.minus(candidatToAdd);
                         if(difference.allPositive()) {
                             resultMinPolyIterator.remove();
                         }
                         else {
                             if(difference.allNegative()) {
                                 insertFlag = false;
                             }
                         }
                     }
                     if(insertFlag) {
                         resultMinPoly.add(candidatToAdd);
                     }
                 }
                resultPoly.add(resultMinPoly);
                }
            }
            return MaxMinPolynomial.create(resultPoly);
        }
    }

    @Override
    public InterpretLabelling getInterpretation (int pos) {
        if(Globals.useAssertions) {
            assert (pos == 0 || pos ==1);
        }
        return (pos==0) ? this.interpret1 : this.interpret2;
    }

    @Override
    public boolean equals(Object other) {
        if (other instanceof MinimumInterpretationInfiniteCarrier) {
            MinimumInterpretationInfiniteCarrier miniIntp = (MinimumInterpretationInfiniteCarrier) other;
            if(this.getInterpretation(0).equals(miniIntp.getInterpretation(0))) {
                if(this.getInterpretation(1).equals(miniIntp.getInterpretation(1))){
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public int hashCode () {
        return ( (41*this.getInterpretation(0).hashCode()) + (103*this.getInterpretation(1).hashCode()) +327 );
    }
}
