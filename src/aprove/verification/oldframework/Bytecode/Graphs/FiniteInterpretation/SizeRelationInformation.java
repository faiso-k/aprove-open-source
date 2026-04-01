package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import org.json.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;


public class SizeRelationInformation implements VariableInformation {

    private AbstractVariableReference lhs;
    private IntegerRelationType rel;
    private SimplePolynomial rhs;

    public SizeRelationInformation(AbstractVariableReference lhs, IntegerRelationType rel, SimplePolynomial rhs) {
        super();
        this.lhs = lhs;
        this.rel = rel;
        this.rhs = rhs;
    }

    public AbstractVariableReference getLhs() {
        return lhs;
    }

    public IntegerRelationType getRel() {
        return rel;
    }

    public SimplePolynomial getRhs() {
        return rhs;
    }

    @Override
    public String toString() {
        return lhs + " " + rel + " " + rhs;
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        // TODO Auto-generated method stub
        return null;
    }

    public Set<String> getVariables() {
        Set<String> res = rhs.getVariables();
        res.add(lhs.toString());
        return res;
    }

}
