package aprove.verification.dpframework.BasicStructures.MaxMinPolynomials;

import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;

public class ConstantInterpretation implements InterpretLabelling{

    private static final Map<Integer,ConstantInterpretation> constMap = new LinkedHashMap<Integer,ConstantInterpretation>();

    public static ConstantInterpretation create(int constant) {
        ConstantInterpretation result = ConstantInterpretation.constMap.get(constant);
        if(result == null) {
            result = new ConstantInterpretation(constant);
            ConstantInterpretation.constMap.put(constant, result);
        }
        return result;
    }

    private int constant;

    private ConstantInterpretation(int constant) {
        this.constant = constant;
    }

    @Override
    public MaxMinPolynomial interpret(MaxMinPolynomial mmp1, MaxMinPolynomial mmp2){
        return MaxMinPolynomial.create(VarPolynomial.create(SimplePolynomial.create(this.constant)));
    }

    @Override
    public boolean equals(Object object) {
        // singleton property!
        return this == object;
    }

    @Override
    public int hashCode() {
        // singleton property
        return super.hashCode();
    }

    @Override
    public String toString() {
        return ("Cons_Intp " + this.constant);
    }

    @Override
    public InterpretLabelling getInterpretation (int pos) {
        return this;
    }

}
