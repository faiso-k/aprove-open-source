package aprove.verification.dpframework.BasicStructures.MaxMinPolynomials;



public class ArgumentInterpretation implements InterpretLabelling{
    private int argNum;

    public ArgumentInterpretation(int argNumber) {
        this.argNum = argNumber;
    }

    @Override
    public MaxMinPolynomial interpret(MaxMinPolynomial mmp1, MaxMinPolynomial mmp2){
        return (this.argNum==1) ? mmp1 : mmp2;
    }

    /*
    @Override
    public String toString() {
        MaxMinPolynomial MMP3;
        return (this.argNum==1) ? (mmp1.t ) : mmp2;

        return null;
    }
    */

    @Override
    public InterpretLabelling getInterpretation (int pos) {
        return this;
    }
}
