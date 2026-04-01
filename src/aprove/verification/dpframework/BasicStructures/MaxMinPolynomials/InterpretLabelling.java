package aprove.verification.dpframework.BasicStructures.MaxMinPolynomials;

public interface InterpretLabelling {
    MaxMinPolynomial interpret (MaxMinPolynomial mmp1, MaxMinPolynomial mmp2 );
    InterpretLabelling getInterpretation(int pos);
}
