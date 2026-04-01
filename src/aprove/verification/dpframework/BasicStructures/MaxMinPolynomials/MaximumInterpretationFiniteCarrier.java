package aprove.verification.dpframework.BasicStructures.MaxMinPolynomials;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * Maximum Interpretation of 2 MaxMinPolynomials over a finite carrier
 *
 * @author Patrick Wiehe
 * @version $Id$
 */
public class MaximumInterpretationFiniteCarrier implements InterpretLabelling{
    private InterpretLabelling interpret1;
    private InterpretLabelling interpret2;
    private final static MaxMinPolynomial ZERO = MaxMinPolynomial.getZERO();

    public MaximumInterpretationFiniteCarrier(InterpretLabelling interpretation1, InterpretLabelling interpretation2) {
        this.interpret1 = interpretation1;
        this.interpret2 = interpretation2;
    }

    @Override
    public MaxMinPolynomial interpret(MaxMinPolynomial mmp1, MaxMinPolynomial mmp2) {
        MaxMinPolynomial argumentValue1 = this.interpret1.interpret(mmp1, mmp2);
        MaxMinPolynomial argumentValue2 = this.interpret2.interpret(mmp1, mmp2);

        //if one of the arguments is ZERO simply return the other.
        if(argumentValue1.equals(MaximumInterpretationFiniteCarrier.ZERO)) {
            return argumentValue2;
        }
        if(argumentValue2.equals(MaximumInterpretationFiniteCarrier.ZERO)) {
            return argumentValue1;
        }

        // if both Polynomials are equal simply return one of them
        if (argumentValue1.equals(argumentValue2)){
            return argumentValue1;

        }
        else {
            Set<Set<VarPolynomial>> resultPoly = new LinkedHashSet<Set<VarPolynomial>>(argumentValue1.getAllMinSets());
            for(Set<VarPolynomial> minsArg2 : argumentValue2.getAllMinSets()) {
                resultPoly.add(minsArg2);
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
        if (other instanceof MaximumInterpretationFiniteCarrier) {
            MaximumInterpretationFiniteCarrier maxiIntp = (MaximumInterpretationFiniteCarrier) other;
            if(this.getInterpretation(0).equals(maxiIntp.getInterpretation(0))) {
                if(this.getInterpretation(1).equals(maxiIntp.getInterpretation(1))){
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public int hashCode () {
        return ( (23*this.getInterpretation(0).hashCode()) + (59*this.getInterpretation(1).hashCode()) +271 );
    }
}
