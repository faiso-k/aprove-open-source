package aprove.verification.dpframework.Orders;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Helper class for the ACRPOS restricted w.r.t. f.
 * @author Stephan Falke
 * @version $Id$
 */
public class ACRPOSf implements MultisetExtensibleOrder<TRSTerm> {

    private ACRPOS acrpos;
    private OrderedSet<FunctionSymbol> p;
    private FunctionSymbol f;

    public ACRPOSf(ACRPOS acrpos, FunctionSymbol f) {
        this.acrpos = acrpos;
        this.p = acrpos.getPrecedence();
        this.f = f;
    }

    @Override
    public OrderRelation compare(TRSTerm s, TRSTerm t) {
        if (s.isVariable() || t.isVariable()) {
            return this.acrpos.compare(s, t);
        }
        FunctionSymbol shead = ((TRSFunctionApplication)s).getRootSymbol();
        FunctionSymbol thead = ((TRSFunctionApplication)t).getRootSymbol();
        if (!shead.equals(this.f)
            && !this.p.isGreater(shead, this.f)
            && !shead.equals(thead)
            && !this.p.isGreater(shead, thead)) {
            return OrderRelation.NGE;
        }
        return this.acrpos.compare(s, t);
    }

    @Override
    public boolean solves(Constraint<TRSTerm> c) {
        throw new RuntimeException("Do not call me!!");
    }

    @Override
    public boolean areEquivalent(TRSTerm s, TRSTerm t) {
        throw new RuntimeException("Do not call me!!");
    }

    @Override
    public boolean inRelation(TRSTerm s, TRSTerm t) {
        throw new RuntimeException("Do not call me!!");
    }

    public StatusMap getStatusMap() {
        return this.acrpos.getStatusMap();
    }

}
