package aprove.verification.complexity.CpxIntTrsProblem.Structures;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;

public class CallArgument implements Exportable {
    public final CpxIntTupleRule rule;
    public final int rhs;
    public final int argument;

    public CallArgument(CpxIntTupleRule rule, int rhs, int argument) {
        assert rule.getRights().size() > rhs && rhs >= 0;
        TRSFunctionApplication fa = rule.getRights().get(rhs);
        assert fa.getRootSymbol().getArity() > argument && argument >= 0;
        this.rule = rule;
        this.rhs = rhs;
        this.argument = argument;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + this.argument;
        result = prime * result + this.rhs;
        result = prime * result + ((this.rule == null) ? 0 : this.rule.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        CallArgument other = (CallArgument) obj;
        if (this.argument != other.argument) {
            return false;
        }
        if (this.rhs != other.rhs) {
            return false;
        }
        if (this.rule == null) {
            if (other.rule != null) {
                return false;
            }
        } else if (!this.rule.equals(other.rule)) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        return this.rule + "|" + this.rhs + "|" + this.argument;
    }

    public LocalSizeBound getLocalSizeBound(Abortion aborter) throws AbortionException {
        return this.rule.getLocalSizeBound(this, aborter);
    }

    public FunctionSymbol getFunctionSymbol() {
        return this.rule.getRights().get(this.rhs).getRootSymbol();
    }

    public TRSTerm getTerm() {
        return this.rule.getRights().get(this.rhs).getArgument(this.argument);
    }

    @Override
    public String export(Export_Util eu) {
        LinkedHashMap<Position, IDPExport.PositionMarker> lhsMarkers = new LinkedHashMap<>();
        LinkedHashMap<Position, IDPExport.PositionMarker> rhsMarkers = new LinkedHashMap<>();
        rhsMarkers.put(Position.create(this.rhs, this.argument), IDPExport.PositionMarker.BOLD_UNDERLINE);
        return this.rule.export(eu, lhsMarkers, rhsMarkers);
    }
}
