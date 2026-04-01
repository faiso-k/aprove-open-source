package aprove.verification.dpframework.BasicStructures.MaxMinPolynomials;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

public class PlusInterpretation implements InterpretLabelling{
    private InterpretLabelling interpret1;
    private InterpretLabelling interpret2;
    private final static MaxMinPolynomial ZERO = MaxMinPolynomial.getZERO();

    public PlusInterpretation(InterpretLabelling interpretation1, InterpretLabelling interpretation2) {
        if(Globals.useAssertions) {
            assert interpretation1 != null;
            assert interpretation2 != null;
        }
        this.interpret1 = interpretation1;
        this.interpret2 = interpretation2;
    }

    @Override
    public MaxMinPolynomial interpret(MaxMinPolynomial mmp1, MaxMinPolynomial mmp2) {
        MaxMinPolynomial argumentValue1 = this.interpret1.interpret(mmp1, mmp2);
        MaxMinPolynomial argumentValue2 = this.interpret2.interpret(mmp1, mmp2);
        Set<Set<VarPolynomial>> resultPoly = new LinkedHashSet<Set<VarPolynomial>>();//to collect the Set of Sets

        //if one of the addends is ZERO simply return the other.
        if(argumentValue1.equals(PlusInterpretation.ZERO)) {
            return argumentValue2;
        }
        if(argumentValue2.equals(PlusInterpretation.ZERO)) {
            return argumentValue1;
        }

        // if both Polynomials are equal simply return poly times 2
        if (argumentValue1.equals(argumentValue2)){
            for(Set<VarPolynomial> mins : argumentValue1.getAllMinSets()) {
                Set<VarPolynomial> minPoly = new LinkedHashSet<VarPolynomial>();//to collect 2*minpoly's
                for(VarPolynomial pol : mins) {
                    minPoly.add(pol.times(SimplePolynomial.create(2)));
                }
                resultPoly.add(minPoly);
            }

        }
        else {
            for(Set<VarPolynomial> minsArg1 : argumentValue1.getAllMinSets()) {
                for(Set<VarPolynomial> minsArg2 : argumentValue2.getAllMinSets()){
                    //check if two min Sets are equal, then simply add 2*minsPoly to resultPoly
                    if(minsArg1.equals(minsArg2)){
                        Set<VarPolynomial> minPoly = new LinkedHashSet<VarPolynomial>();//to collect 2*varpoly's
                        for(VarPolynomial pol : minsArg1){
                            minPoly.add(pol.times(SimplePolynomial.create(2)));
                        }
                        resultPoly.add(minPoly);
                    }
                    else {
                        Set<VarPolynomial> minPoly = new LinkedHashSet<VarPolynomial>();//to collect the sum
                        for(VarPolynomial varPolyArg1 : minsArg1) {

                            for(VarPolynomial varPolyArg2 : minsArg2){
                                minPoly.add(varPolyArg1.plus(varPolyArg2));
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
        return ("Plus_Intp with : " + this.interpret1.toString() + " and " + this.interpret2.toString());
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
        if (other instanceof PlusInterpretation) {
            PlusInterpretation plusIntp = (PlusInterpretation) other;
            if(this.getInterpretation(0).equals(plusIntp.getInterpretation(0))) {
                if(this.getInterpretation(1).equals(plusIntp.getInterpretation(1))){
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public int hashCode () {
        return ( (43*this.getInterpretation(0).hashCode()) + (69*this.getInterpretation(1).hashCode()) +394 );
    }
}
