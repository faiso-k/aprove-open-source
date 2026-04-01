package aprove.verification.dpframework.BasicStructures.Matchbounds;

import aprove.verification.oldframework.BasicStructures.*;

// is a pair of a functionsymbol and a nr
public class AnnotatedFunctionSymbol {

    public final FunctionSymbol f;
    public final int nr;

    public AnnotatedFunctionSymbol(FunctionSymbol f, int nr) {
        this.f = f;
        this.nr = nr;
    }

    @Override
    public String toString() {
        return this.f+"("+this.nr+")";
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if (other instanceof AnnotatedFunctionSymbol) {
            AnnotatedFunctionSymbol sym = (AnnotatedFunctionSymbol) other;
            return this.nr == sym.nr && this.f.equals(sym.f);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return this.nr | (this.f.hashCode() << 4);
    }

}
