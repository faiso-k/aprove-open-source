package aprove.verification.dpframework.MCSProblem;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Possible relations for use in a single MC order constraint.
 *
 * @author fuhs
 */
public enum MCRelation implements Exportable {
    LT(RepresentationHolder.LT_REP),
    LE(RepresentationHolder.LE_REP),
    EQ(RepresentationHolder.EQ_REP),
    GE(RepresentationHolder.GE_REP),
    GT(RepresentationHolder.GT_REP);


    private final String rep;

    private MCRelation(String rep) {
        this.rep = rep;
    }

    public static MCRelation fromRepresentation(String rep) {
        if (LT.getRepresentation().equals(rep)) {
            return LT;
        } else if (LE.getRepresentation().equals(rep)) {
            return LE;
        } else if (EQ.getRepresentation().equals(rep)) {
            return EQ;
        } else if (GE.getRepresentation().equals(rep)) {
            return GE;
        } else if (GT.getRepresentation().equals(rep)) {
            return GT;
        } else {
            throw new IllegalArgumentException("Unknown MCRelation representation " + rep + '!');
        }
    }

    public MCRelation invert() {
        switch(this) {
        case LT : return GT;
        case LE : return GE;
        case EQ : return EQ;
        case GE : return LE;
        case GT : return LT;
        default : throw new UnsupportedOperationException("Unknown relation " + this);
        }
    }

    public String getRepresentation() {
        return this.toString();
    }

    /**
     * @param predefMap
     * @return the corresponding function symbol according to
     *  <code>predefMap</code>
     */
    public FunctionSymbol toFunctionSymbol(IDPPredefinedMap predefMap) {
        switch (this) {
        case LT : return predefMap.getSym(Func.Lt, DomainFactory.INTEGERS);
        case LE : return predefMap.getSym(Func.Le, DomainFactory.INTEGERS);
        case EQ : return predefMap.getSym(Func.Eq, DomainFactory.INTEGERS);
        case GE : return predefMap.getSym(Func.Ge, DomainFactory.INTEGERS);
        case GT : return predefMap.getSym(Func.Gt, DomainFactory.INTEGERS);
        default : throw new UnsupportedOperationException("Unknown relation " + this);
        }
    }

    @Override
    public String toString() {
        return this.rep;
    }

    @Override
    public String export(Export_Util o) {
        switch(this) {
        case LT : return o.ltSign();
        case LE : return o.leSign();
        case EQ : return o.eqSign();
        case GE : return o.geSign();
        case GT : return o.gtSign();
        default : throw new UnsupportedOperationException("Unknown relation " + this);
        }
    }

    /**
     * Java does not seem to like enums that use constants defined only after
     * their instances -- and it does not seem to allow defining constants
     * before said instances either. Hence this class ...
     */
    private class RepresentationHolder {
        private final static String LT_REP = "<";
        private final static String LE_REP = "<=";
        private final static String EQ_REP = "=";
        private final static String GE_REP = ">=";
        private final static String GT_REP = ">";
    }
}
