package aprove.verification.dpframework.BasicStructures.MaxMinPolynomials;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

public class MonosInterpretation implements InterpretLabelling{

    private InterpretLabelling interpret1;
    private InterpretLabelling interpret2;
    private final static MaxMinPolynomial ZERO = MaxMinPolynomial.getZERO();

    public MonosInterpretation(InterpretLabelling interpretation1, InterpretLabelling interpretation2) {
        this.interpret1 = interpretation1;
        this.interpret2 = interpretation2;
    }

    @Override
    public MaxMinPolynomial interpret(MaxMinPolynomial mmp1, MaxMinPolynomial mmp2) {
        MaxMinPolynomial argumentValue1 = this.interpret1.interpret(mmp1, mmp2);
        MaxMinPolynomial argumentValue2 = this.interpret2.interpret(mmp1, mmp2);
        Set<Set<VarPolynomial>> resultPoly = new LinkedHashSet<Set<VarPolynomial>>();//to collect the Set of Sets
        boolean onlyVpsWithAllPositiveSeen = true;
        boolean completelyPositiveMinSetSeen = false;

        if(argumentValue1.equals(MonosInterpretation.ZERO)) {
            return argumentValue1;
        }
        if(argumentValue2.equals(MonosInterpretation.ZERO)) {
            return argumentValue1;
        }
        if(argumentValue1.equals(argumentValue2)) {
            return MonosInterpretation.ZERO;
        }
        else {
            for(Set<VarPolynomial> minsArg1 : argumentValue1.getAllMinSets()) {
                for(Set<VarPolynomial> minsArg2 : argumentValue2.getAllMinSets()){
                    //check if two min Sets are equal, result would be zero, simply do nothing.
                    if(minsArg1.equals(minsArg2)){
                        continue;
                    }

                    else {
                        VarPolynomial difference;
                        Set<VarPolynomial> minPoly = new LinkedHashSet<VarPolynomial>();//to collect minsThis-minsPoly
                        for(VarPolynomial varPolyOfArg1 : minsArg1) {
                            for(VarPolynomial varPolyOfArg2 : minsArg2){
                                difference = varPolyOfArg1.minus(varPolyOfArg2);
                                if(onlyVpsWithAllPositiveSeen) {
                                    onlyVpsWithAllPositiveSeen = difference.allPositive();
                                }
                                minPoly.add(difference);
                            }
                        }
                        resultPoly.add(minPoly);
                        if(onlyVpsWithAllPositiveSeen) {
                            completelyPositiveMinSetSeen = true;
                        }
                    }
                }
            }
            if(completelyPositiveMinSetSeen) {
                return MaxMinPolynomial.create(resultPoly);
            }
            else {
                Set<VarPolynomial> auxMinPoly = new LinkedHashSet<VarPolynomial>(1);
                auxMinPoly.add(VarPolynomial.ZERO);
                resultPoly.add(auxMinPoly);
                return MaxMinPolynomial.create(resultPoly);
            }
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
        if (other instanceof MonosInterpretation) {
            MonosInterpretation monosIntp = (MonosInterpretation) other;
            if(this.getInterpretation(0).equals(monosIntp.getInterpretation(0))) {
                if(this.getInterpretation(1).equals(monosIntp.getInterpretation(1))){
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public int hashCode () {
        return ( (47*this.getInterpretation(0).hashCode()) + (97*this.getInterpretation(1).hashCode()) +17 );
    }
}
