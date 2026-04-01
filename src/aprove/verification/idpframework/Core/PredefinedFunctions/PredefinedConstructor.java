package aprove.verification.idpframework.Core.PredefinedFunctions;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public abstract class PredefinedConstructor<D extends SemiRing<D>> extends
        PredefinedSemantics<D> {

    public static final ImmutableArrayList<ITerm<?>> EMPTY_ARGLIST =
        ImmutableCreator.create(new ArrayList<ITerm<?>>());
    protected final SemiRingDomain<D> domain;

    protected PredefinedConstructor(final int arity, final SemiRingDomain<D> domain) {
        super(arity);
        this.domain = domain;
    }

    @Override
    public SemiRingDomain<D> getResultDomain() {
        return this.domain;
    }

    @Override
    public ImmutableList<? extends SemiRingDomain<?>> getDomains() {
        return ImmutableCreator.create(Collections.<SemiRingDomain<?>> emptyList());
    }

    public abstract IFunctionSymbol<?> getSym();

    public abstract String getName();

    public abstract IFunctionApplication<?> getTerm();

    @Override
    public boolean isConstructor() {
        return true;
    }

}
