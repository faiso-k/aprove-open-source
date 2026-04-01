package aprove.verification.oldframework.DifferenceUnification;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

public class PairOfTermsWithPositions {

    protected AlgebraTerm leftTerm;
    protected AlgebraTerm rightTerm;

    protected Position leftPosition;
    protected Position rightPosition;

    protected Set<AlgebraVariable> usedVariables;

    protected PairOfTermsWithPositions(AlgebraTerm leftTerm, AlgebraTerm rightTerm, Position leftPosition, Position rightPosition) {

        this.leftTerm      = leftTerm;
        this.rightTerm     = rightTerm;
        this.leftPosition  = leftPosition;
        this.rightPosition = rightPosition;

        this.usedVariables = new LinkedHashSet<AlgebraVariable>();
        this.usedVariables.addAll(this.leftTerm.getVars());
        this.usedVariables.addAll(this.rightTerm.getVars());

    }

    protected PairOfTermsWithPositions() {
    }

    public static PairOfTermsWithPositions create(AlgebraTerm leftTerm, AlgebraTerm rightTerm, Position leftPosition, Position rightPosition) {
        return new PairOfTermsWithPositions(leftTerm,rightTerm,leftPosition, rightPosition);
    }

    public PairOfTermsWithPositions deepcopy() {
        PairOfTermsWithPositions copy = new PairOfTermsWithPositions();
        copy.leftTerm      = this.leftTerm;
        copy.rightTerm     = this.rightTerm;
        copy.leftPosition  = this.leftPosition.shallowcopy();
        copy.rightPosition = this.rightPosition.shallowcopy();
        copy.usedVariables = new LinkedHashSet<AlgebraVariable>(this.usedVariables);
        return copy;
    }

    @Override
    public boolean equals(Object object) {
        if( object instanceof PairOfTermsWithPositions) {
            PairOfTermsWithPositions that = (PairOfTermsWithPositions)object;
            return this.leftTerm.equals(that.leftTerm) && this.rightTerm.equals(that.rightTerm) &&
                this.rightPosition.equals(that.rightPosition) && this.leftPosition.equals(that.leftPosition);
        }else{
            return false;
        }
    }

    @Override
    public int hashCode() {
        return this.leftTerm.hashCode() + this.rightTerm.hashCode();
    }

    @Override
    public String toString() {
        StringBuffer stringBuffer = new StringBuffer();
        stringBuffer.append("(");
        stringBuffer.append(this.leftTerm.toString()+",");
        stringBuffer.append(this.rightTerm.toString()+"/");
        stringBuffer.append(this.leftPosition.toString()+",");
        stringBuffer.append(this.rightPosition.toString()+")");
        return stringBuffer.toString();
    }

    public Set<AlgebraVariable> getAllUsedVariables() {
        return new LinkedHashSet<AlgebraVariable>(this.usedVariables);
    }
}