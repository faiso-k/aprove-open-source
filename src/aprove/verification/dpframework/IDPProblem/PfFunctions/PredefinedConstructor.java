package aprove.verification.dpframework.IDPProblem.PfFunctions;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.oldframework.BasicStructures.*;


/**
 *
 * @author Martin Pluecker
 */
public abstract class PredefinedConstructor extends PredefinedSemantics {

    protected final Domain domain;

    protected PredefinedConstructor(int arity, Domain domain) {
        super(arity);
        this.domain = domain;
    }

    @Override
    public boolean isConstructor() {
        return true;
    }

    @Override
    public boolean isFunction() {
        return false;
    }

    public Domain getDomain() {
        return this.domain;
    }

    public abstract FunctionSymbol getSym();
    public abstract TRSFunctionApplication getTerm();

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

}
