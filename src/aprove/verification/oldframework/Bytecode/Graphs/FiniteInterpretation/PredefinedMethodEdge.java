package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

@SuppressWarnings("serial")
public class PredefinedMethodEdge extends EvaluationEdge {

    private SimplePolynomial lowerTimeBound;
    private SimplePolynomial upperTimeBound;
    private SimplePolynomial lowerSpaceBound;
    private SimplePolynomial upperSpaceBound;
    private Map<AbstractVariableReference, AbstractVariableReference> refRenaming;
    private boolean isStatic;
    private int numArgs;
    private boolean isVoid;
    private String additionalLabel;

    public PredefinedMethodEdge(SimplePolynomial lowerTimeBound,
            SimplePolynomial upperTimeBound,
            SimplePolynomial lowerSpaceBound,
            SimplePolynomial upperSpaceBound,
            boolean isStatic,
            boolean isVoid,
            int numArgs) {
        this.lowerTimeBound = lowerTimeBound;
        this.upperTimeBound = upperTimeBound;
        this.lowerSpaceBound = lowerSpaceBound;
        this.upperSpaceBound = upperSpaceBound;
        this.isStatic = isStatic;
        this.isVoid = isVoid;
        this.numArgs = numArgs;
    }

    @Override
    public String toString() {
        String res = "";
        if (additionalLabel != null) {
            res += additionalLabel + "\n";
        }
        res += "Time: [" + lowerTimeBound + ", " + upperTimeBound + "], Space: [" + lowerSpaceBound + ", " + upperSpaceBound + "]";
        return res;
    }

    public SimplePolynomial getUpperSpaceBound() {
        return upperSpaceBound;
    }

    public Map<AbstractVariableReference, AbstractVariableReference> getRefRenaming() {
        return refRenaming;
    }

    public void setRefRenaming(Map<AbstractVariableReference, AbstractVariableReference> refRenaming) {
        this.refRenaming = refRenaming;
    }

    public SimplePolynomial getLowerSpaceBound() {
        return lowerSpaceBound;
    }

    public SimplePolynomial getLowerTimeBound() {
        return lowerTimeBound;
    }

    public SimplePolynomial getUpperTimeBound() {
        return upperTimeBound;
    }

    public boolean isStatic() {
        return isStatic;
    }

    public boolean isVoid() {
        return isVoid;
    }

    public int getNumArgs() {
        return numArgs;
    }

    public String getAdditionalLabel() {
        return additionalLabel;
    }

    public void setAdditionalLabel(String additionalLabel) {
        this.additionalLabel = additionalLabel;
    }
}
