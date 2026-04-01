package aprove.verification.dpframework.BasicStructures.MaxMinPolynomials;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import immutables.*;

/**
 * Maximum Interpretation of 2 MaxMinPolynomials over the infinite carrier natural numbers
 *
 * @author Patrick Wiehe
 * @version $Id$
 */
public class MaximumInterpretationInfiniteCarrier implements InterpretLabelling{

    private InterpretLabelling interpret1;
    private InterpretLabelling interpret2;
    private final static MaxMinPolynomial ZERO = MaxMinPolynomial.getZERO();

    public MaximumInterpretationInfiniteCarrier(InterpretLabelling interpretation1, InterpretLabelling interpretation2) {
        this.interpret1 = interpretation1;
        this.interpret2 = interpretation2;
    }

    @Override
    public MaxMinPolynomial interpret(MaxMinPolynomial mmp1, MaxMinPolynomial mmp2) {
        MaxMinPolynomial argumentValue1 = this.interpret1.interpret(mmp1, mmp2);
        MaxMinPolynomial argumentValue2 = this.interpret2.interpret(mmp1, mmp2);

        //if one of the arguments is ZERO simply return the other.
        if(argumentValue1.equals(MaximumInterpretationInfiniteCarrier.ZERO)) {
            return argumentValue2;
        }
        if(argumentValue2.equals(MaximumInterpretationInfiniteCarrier.ZERO)) {
            return argumentValue1;
        }

        // if both Polynomials are equal simply return one of them
        if (argumentValue1.equals(argumentValue2)){
            return argumentValue1;

        }
        else {
            LinkedHashSet<ImmutableMap<String, ImmutableList<VarPolynomial>>> aux1 =
                new LinkedHashSet<ImmutableMap<String,ImmutableList<VarPolynomial>>>(mmp1.getVariableMapping());
            LinkedHashSet<ImmutableMap<String, ImmutableList<VarPolynomial>>> aux2 =
                new LinkedHashSet<ImmutableMap<String,ImmutableList<VarPolynomial>>>(mmp2.getVariableMapping());
            Iterator<ImmutableMap<String, ImmutableList<VarPolynomial>>> iter1 = aux1.iterator();
            Iterator<ImmutableMap<String, ImmutableList<VarPolynomial>>> iter2;

            LinkedHashSet<LinkedHashSet<VarPolynomial>> newMMP = new LinkedHashSet<LinkedHashSet<VarPolynomial>>();

            boolean map1Dommap2;
            boolean map2Dommap1;
            boolean lastOfSet1;
            boolean lastOfSet2;
            while(iter1.hasNext()) {
                map2Dommap1 = false;
                map1Dommap2 = false;
                ImmutableMap<String, ImmutableList<VarPolynomial>> map1 = iter1.next();
                lastOfSet1 = (! iter1.hasNext());
                iter2 = aux2.iterator();
                while((!map2Dommap1) && iter2.hasNext()) {
                    ImmutableMap<String, ImmutableList<VarPolynomial>> map2 = iter2.next();
                    map2Dommap1 = MaxMinPolynomial.minTermDomination(map1, map2);
                    if(map2Dommap1) {
                        iter1.remove();
                        if(lastOfSet1) {// we have to collect the remaining minSets here,
                                       // otherwise they would get lost!

                            //Collect the actual minSet since it is not dominated by any minSet of mmp1.
                            LinkedHashSet<VarPolynomial> newMinSet = new LinkedHashSet<VarPolynomial>();
                            for(ImmutableList<VarPolynomial> actList : map2.values()) {
                                for(VarPolynomial vp : actList) {
                                    newMinSet.add(vp);
                                }
                            }
                            newMMP.add(newMinSet);
                            //Collect the remaining minSets, which are also not dominated.
                            while(iter2.hasNext()) {
                                map2 = iter2.next();
                                newMinSet = new LinkedHashSet<VarPolynomial>();
                                for(ImmutableList<VarPolynomial> actList : map2.values()) {
                                    for(VarPolynomial vp : actList) {
                                        newMinSet.add(vp);
                                    }
                                }
                                newMMP.add(newMinSet);
                            }
                        }

                    }
                    else {//check the other way round
                        map1Dommap2 = MaxMinPolynomial.minTermDomination(map2, map1);
                        if(map1Dommap2) {
                            iter2.remove();
                            // do not set dom to false here!
                            // One minSet can dominate more than one other minSet
                            // e.g. {ax} > {ax, by}  &  {ax} > {ax, cz}
                            // So we still have to check the other minSets of mmp2!
                            lastOfSet2 = aux2.isEmpty();
                            if(lastOfSet2) {// we have to collect the remaining minSets here,
                                // otherwise they would get lost!

                                //Collect the actual minSet since it is not dominated by any minSet of mmp2.
                                LinkedHashSet<VarPolynomial> newMinSet = new LinkedHashSet<VarPolynomial>();
                                for(ImmutableList<VarPolynomial> actList : map1.values()) {
                                    for(VarPolynomial vp : actList) {
                                        newMinSet.add(vp);
                                    }
                                }
                                newMMP.add(newMinSet);
                                //Collect the remaining minSets, which are also not dominated.
                                while(iter1.hasNext()) {
                                    map1 = iter1.next();
                                    newMinSet = new LinkedHashSet<VarPolynomial>();
                                    for(ImmutableList<VarPolynomial> actList : map1.values()) {
                                        for(VarPolynomial vp : actList) {
                                            newMinSet.add(vp);
                                        }
                                    }
                                    newMMP.add(newMinSet);
                                }
                            }
                        }
                        else {
                            if(lastOfSet1) {
                                // the minSet represented by map2 is not dominated by any minSet of mmp1!
                                // So we have to keep it, and since we have it located right here we might
                                // as well save it in newMMP right now.
                                LinkedHashSet<VarPolynomial> newMinSet = new LinkedHashSet<VarPolynomial>();
                                for(ImmutableList<VarPolynomial> actList : map2.values()) {
                                    for(VarPolynomial vp : actList) {
                                        newMinSet.add(vp);
                                    }
                                }
                                newMMP.add(newMinSet);
                            }
                        }
                    }
                }
                if(!map2Dommap1) {
                    // the minSet represented by map1 is not dominated by any minSet of mmp2!
                    // So we have to keep it, and since we have it located right here we might
                    // as well save it in newMMP right now.
                    LinkedHashSet<VarPolynomial> newMinSet = new LinkedHashSet<VarPolynomial>();
                    for(ImmutableList<VarPolynomial> actList : map1.values()) {
                        for(VarPolynomial vp : actList) {
                            newMinSet.add(vp);
                        }
                    }
                    newMMP.add(newMinSet);
                }
            }
            //build the new mmp out of the remainig minSets
            return MaxMinPolynomial.create(newMMP);
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
        if (other instanceof MaximumInterpretationInfiniteCarrier) {
            MaximumInterpretationInfiniteCarrier miniIntp = (MaximumInterpretationInfiniteCarrier) other;
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
        return ( (67*this.getInterpretation(0).hashCode()) + (83*this.getInterpretation(1).hashCode()) +327 );
    }

}
