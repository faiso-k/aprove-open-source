package aprove.prooftree.Obligations.Junctors;

import aprove.verification.oldframework.Logic.*;

public class Junctors {

    public static IJunctor AND = new AndJunctor();
    public static IJunctor OR = new OrJunctor();
    public static IJunctor COND = new CondJunctor();

    public static IJunctor MAX_UPPER = new MaxUpperJunctor();
    public static IJunctor MIN_UPPER = new MinUpperJunctor();
    public static IJunctor MULT_UPPER = new MultUpperJunctor();
    public static IJunctor BEST = new BestComplexityJunctor();

    public static IJunctor YES = Junctors.FIXED_VALUE(YNM.YES);
    public static IJunctor NO = Junctors.FIXED_VALUE(YNM.NO);
    public static IJunctor MAYBE = Junctors.FIXED_VALUE(YNM.MAYBE);

    public static IJunctor FIXED_VALUE(TruthValue tv) {
        return new FixedValueJunctor(tv);
    }

    private Junctors() {};
}
