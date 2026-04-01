package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import org.json.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;


public class EnvrionmentChangeInformation implements VariableInformation {

    private Optional<SimplePolynomial> lb;
    private Optional<SimplePolynomial> ub;

    public EnvrionmentChangeInformation(Optional<SimplePolynomial> lb, Optional<SimplePolynomial> ub) {
        this.lb = lb;
        this.ub = ub;
    }

    public Optional<SimplePolynomial> getLb() {
        return lb;
    }

    public Optional<SimplePolynomial> getUb() {
        return ub;
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        // TODO Auto-generated method stub
        return null;
    }

}
