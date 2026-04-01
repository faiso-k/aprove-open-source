package aprove.verification.dpframework.BasicStructures;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import immutables.*;

/**
 * This class represents an immutable afs.
 *
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public final class ImmutableAfs extends Afs {

    public ImmutableAfs(Afs afs) {
        this.filters = ImmutableCreator.create(afs.filters);
    }

    @Override
    public void setNoFiltering(FunctionSymbol f) {
        throw new UnsupportedOperationException("SetNoFiltering operation is not allowed in immutable collections.");
    }

    @Override
    public void setCollapsing(FunctionSymbol f, int pos) {
        throw new UnsupportedOperationException("SetCollapsing operation is not allowed in immutable collections.");
    }

    @Override
    public void setFiltering(FunctionSymbol f, YNM[] args) {
        throw new UnsupportedOperationException("SetFiltering operation is not allowed in immutable collections.");
    }

}
