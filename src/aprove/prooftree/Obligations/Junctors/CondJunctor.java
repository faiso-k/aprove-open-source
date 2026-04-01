package aprove.prooftree.Obligations.Junctors;

import java.util.*;

import aprove.verification.oldframework.Logic.*;

public class CondJunctor implements IJunctor {

    CondJunctor() {}

    @Override
    public TruthValue combine(List<? extends TruthValue> truthValues) {
        if (truthValues.size() != 2) {
            throw new IllegalArgumentException("COND must have exactly 2 nodes!");
        }

        TruthValue other = truthValues.get(1);
        if(truthValues.get(0).equals(YNM.YES)){
            if(other.equals(YNM.YES)){
                return YNM.YES;
            }
            if(other.equals(YNM.NO)){
                return YNM.NO;
            }
            return YNM.MAYBE;
        }
        return YNM.MAYBE;
    }

    @Override
    public String getName(int numTruthValues){
        return "COND";
    }

}
