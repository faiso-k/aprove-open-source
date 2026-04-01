package aprove.verification.dpframework.BasicStructures.MaxMinPolynomials;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * Minimum Interpretation of 2 MaxMinPolynomials over a finite carrier
 *
 * @author Patrick Wiehe
 * @version $Id$
 */
public class MinimumInterpretationFiniteCarrier implements InterpretLabelling{
    private InterpretLabelling interpret1;
    private InterpretLabelling interpret2;
    private final static MaxMinPolynomial ZERO = MaxMinPolynomial.getZERO();

    public MinimumInterpretationFiniteCarrier(InterpretLabelling interpretation1, InterpretLabelling interpretation2) {
        this.interpret1 = interpretation1;
        this.interpret2 = interpretation2;
    }

    @Override
    public MaxMinPolynomial interpret(MaxMinPolynomial mmp1, MaxMinPolynomial mmp2) {
        MaxMinPolynomial argumentValue1 = this.interpret1.interpret(mmp1, mmp2);
        MaxMinPolynomial argumentValue2 = this.interpret2.interpret(mmp1, mmp2);

        if(argumentValue1.equals(MinimumInterpretationFiniteCarrier.ZERO)) {
            return argumentValue1;
        }
        if(argumentValue2.equals(MinimumInterpretationFiniteCarrier.ZERO)) {
            return argumentValue2;
        }
        if(argumentValue1.equals(argumentValue2)) {
            return argumentValue1;
        }
        else {
            Set<Set<VarPolynomial>> resultPoly = new LinkedHashSet<Set<VarPolynomial>>();//to collect the Set of Sets
            for(Set<VarPolynomial> minsArg1 : argumentValue1.getAllMinSets()){
                for(Set<VarPolynomial> minsArg2 : argumentValue2.getAllMinSets()){
                 Set<VarPolynomial> resultMinPoly = new LinkedHashSet<VarPolynomial>(); //to collect union of VarPoly of minsArg1
                    resultMinPoly.addAll(minsArg1);                                     //and VarPoly of minsArg2
                    resultMinPoly.addAll(minsArg2);
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
        if (other instanceof MinimumInterpretationFiniteCarrier) {
            MinimumInterpretationFiniteCarrier miniIntp = (MinimumInterpretationFiniteCarrier) other;
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
        return ( (37*this.getInterpretation(0).hashCode()) + (83*this.getInterpretation(1).hashCode()) +327 );
    }
}
