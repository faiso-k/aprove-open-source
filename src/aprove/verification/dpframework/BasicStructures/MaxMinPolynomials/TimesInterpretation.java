package aprove.verification.dpframework.BasicStructures.MaxMinPolynomials;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

public class TimesInterpretation implements InterpretLabelling {
    private InterpretLabelling interpret1;
    private InterpretLabelling interpret2;
    private final static MaxMinPolynomial ZERO = MaxMinPolynomial.getZERO();
    private final static MaxMinPolynomial ONE = MaxMinPolynomial.getONE();

    public TimesInterpretation(InterpretLabelling interpretation1, InterpretLabelling interpretation2) {
        this.interpret1 = interpretation1;
        this.interpret2 = interpretation2;
    }

    @Override
    public MaxMinPolynomial interpret(MaxMinPolynomial mmp1, MaxMinPolynomial mmp2) {
        MaxMinPolynomial argumentValue1 = this.interpret1.interpret(mmp1, mmp2);
        MaxMinPolynomial argumentValue2 = this.interpret2.interpret(mmp1, mmp2);
        Set<Set<VarPolynomial>> resultPoly = new LinkedHashSet<Set<VarPolynomial>>();//to collect the Set of Sets

        if(argumentValue1.equals(TimesInterpretation.ZERO) || argumentValue2.equals(TimesInterpretation.ZERO)) {
            return TimesInterpretation.ZERO;
        }
        if(argumentValue1.equals(TimesInterpretation.ONE)) {
            return argumentValue2;
        }
        if(argumentValue2.equals(TimesInterpretation.ONE)) {
            return argumentValue1;
        }
        if(argumentValue1.equals(argumentValue2)){
            for(Set<VarPolynomial> mins : argumentValue1.getAllMinSets()) {
                Set<VarPolynomial> minPoly = new LinkedHashSet<VarPolynomial>();//to collect minpoly's to the power of 2
                for(VarPolynomial pol : mins) {
                    minPoly.add(pol.times(pol));
                }
                resultPoly.add(minPoly);
            }
        }

        else {
            for(Set<VarPolynomial> minsArg1 : argumentValue1.getAllMinSets()) {
                for(Set<VarPolynomial> minsArg2 : argumentValue2.getAllMinSets()){
                    //check if two min Sets are equal, then simply add pol*pol to resultPoly
                    if(minsArg1.equals(minsArg2)){
                        Set<VarPolynomial> minPoly = new LinkedHashSet<VarPolynomial>();//to collect varpoly's to the power of 2
                        for(VarPolynomial pol : minsArg1){
                            minPoly.add(pol.times(pol));
                        }
                        resultPoly.add(minPoly);
                    }

                    else {
                        Set<VarPolynomial> minPoly = new LinkedHashSet<VarPolynomial>();//to collect product of polys
                        for(VarPolynomial varPolyThis : minsArg1) {
                            for(VarPolynomial varPolyOther : minsArg2){
                                minPoly.add(varPolyOther.times(varPolyThis));
                            }
                        }
                        resultPoly.add(minPoly);
                    }
                }
            }
            }
        return MaxMinPolynomial.create(resultPoly);
    }

    @Override
    public String toString () {
        return ("Times_Intp with : " + this.interpret1.toString() + " and " + this.interpret2.toString());
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
        if (other instanceof TimesInterpretation) {
            TimesInterpretation timesIntp = (TimesInterpretation) other;
            if(this.getInterpretation(0).equals(timesIntp.getInterpretation(0))) {
                if(this.getInterpretation(1).equals(timesIntp.getInterpretation(1))){
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public int hashCode () {
        return ( (41*this.getInterpretation(0).hashCode()) + (67*this.getInterpretation(1).hashCode()) +523 );
    }
}
