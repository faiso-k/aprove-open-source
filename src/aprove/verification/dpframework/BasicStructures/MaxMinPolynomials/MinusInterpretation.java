package aprove.verification.dpframework.BasicStructures.MaxMinPolynomials;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

public class MinusInterpretation implements InterpretLabelling{


    private InterpretLabelling interpret1;
    private InterpretLabelling interpret2;
    private final static MaxMinPolynomial ZERO = MaxMinPolynomial.getZERO();

    public MinusInterpretation(InterpretLabelling interpretation1, InterpretLabelling interpretation2) {
        this.interpret1 = interpretation1;
        this.interpret2 = interpretation2;
    }

    @Override
    public MaxMinPolynomial interpret(MaxMinPolynomial mmp1, MaxMinPolynomial mmp2) {
        MaxMinPolynomial argumentValue1 = this.interpret1.interpret(mmp1, mmp2);
        MaxMinPolynomial argumentValue2 = this.interpret2.interpret(mmp1, mmp2);
        Set<Set<VarPolynomial>> resultPoly = new LinkedHashSet<Set<VarPolynomial>>();//to collect the Set of Sets
        if(argumentValue1.equals(MinusInterpretation.ZERO)) {
            //Simply subtract each VarPolynomial of mmp2 from 0
            for(Set<VarPolynomial> minsArg2 : argumentValue2.getAllMinSets()){
                VarPolynomial difference;
                Set<VarPolynomial> minPoly = new LinkedHashSet<VarPolynomial>();//to collect minsThis-minsPoly
                for(VarPolynomial varPolyOfArg2 : minsArg2){
                    difference = VarPolynomial.ZERO.minus(varPolyOfArg2);
                    minPoly.add(difference);
                }
                resultPoly.add(minPoly);
            }
            return MaxMinPolynomial.create(resultPoly);
        }
        if(argumentValue2.equals(MinusInterpretation.ZERO)) {
            return argumentValue1;
        }
        if(argumentValue1.equals(argumentValue2)) {
            return MinusInterpretation.ZERO;
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
                                minPoly.add(difference);
                            }
                        }
                        resultPoly.add(minPoly);
                    }
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
        if (other instanceof MinusInterpretation) {
            MinusInterpretation minusIntp = (MinusInterpretation) other;
            if(this.getInterpretation(0).equals(minusIntp.getInterpretation(0))) {
                if(this.getInterpretation(1).equals(minusIntp.getInterpretation(1))){
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public int hashCode () {
        return ( (49*this.getInterpretation(0).hashCode()) + (91*this.getInterpretation(1).hashCode()) +23);
    }

}
