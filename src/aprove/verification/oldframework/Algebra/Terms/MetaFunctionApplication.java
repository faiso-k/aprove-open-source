package aprove.verification.oldframework.Algebra.Terms;

import java.util.*;

import aprove.verification.oldframework.Syntax.*;

public class MetaFunctionApplication extends AlgebraFunctionApplication {

    public static MetaFunctionApplication create(MetaFunctionSymbol sym, AlgebraTerm arg) {
        Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
        args.add(arg);
        return new MetaFunctionApplication(sym,args);
    }

    public static MetaFunctionApplication create(MetaFunctionSymbol sym, List<? extends AlgebraTerm> args) {
        return new MetaFunctionApplication(sym,args);
    }

    protected MetaFunctionApplication(MetaFunctionSymbol sym, List<? extends AlgebraTerm> args) {
        super(sym, args);
    }

    @Override
    public <T> T apply(FineGrainedTermVisitor<T> ftv) {
        return ftv.caseMetaFunctionApplication(this);
    }

    @Override
    public String verboseToString() {
        return null;
    }

    @Override
    public boolean isTerminating() {
        return false;
    }

    @Override
    public boolean isConstructorTerm() {
        return false;
    }

    @Override
    public boolean isGroundTerm() {
        return false;
    }

    @Override
    public boolean isMetaFunctionApplication() {
        return true;
    }

    public MetaFunctionSymbol getMetaFunctionSymbol() {
        return (MetaFunctionSymbol)this.sym;
    }

    @Override
    final public boolean equals(Object o) {
        if(o instanceof MetaFunctionApplication) {
            MetaFunctionApplication t = (MetaFunctionApplication)o;
            return this.getSymbol().equals(t.getSymbol()) && this.args.equals(t.getArguments());
        }else{
            return false;
        }
    }
}
