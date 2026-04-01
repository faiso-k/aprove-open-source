package aprove.verification.dpframework.Orders ;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
/** Helper class for the ACQRPOS restricted w.r.t. f.
 *
 * @author Stephan Falke
 *  @version $Id$
 */
public class ACQRPOSf implements MultisetExtensibleOrder<TRSTerm> {

    private ACQRPOS acqrpos;
    private Qoset<String> p;
    private String f;

    public ACQRPOSf(ACQRPOS acqrpos, String f) {
    this.acqrpos = acqrpos;
    this.p = (Qoset<String>)acqrpos.getPrecedence();
    this.f = f;
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

    @Override
    public OrderRelation compare(TRSTerm s, TRSTerm t) {
        String shead;
        if (s.isVariable()) {
            shead = ((TRSVariable)s).getName();
        } else {
            shead = ((TRSFunctionApplication)s).getRootSymbol().getName();
        }
        String thead;
        if (t.isVariable()) {
            thead = ((TRSVariable)t).getName();
        } else {
            thead = ((TRSFunctionApplication)t).getRootSymbol().getName();
        }
    if(!shead.equals(this.f) && !s.isVariable() && !this.p.isGreater(shead, this.f) && !shead.equals(thead) && !t.isVariable() && !this.p.isGreater(shead, thead) && !this.p.areEquivalent(shead, thead)) {
        return OrderRelation.NGE;
    }
    return this.acqrpos.compare(s, t);
    }

    public String toHTML() {
    return "You should never have seen this!";
    }

    public StatusMap getStatusMap() {
    return this.acqrpos.getStatusMap();
    }

    public OrderedSet<String> getPrecedence() {
        return this.acqrpos.getPrecedence();
    }

    public String toLaTeX() {
    return "If you see this, something is wrong!";
    }

    public String toBibTeX(){
        return "";
    }
}
