/**
 *
 */
package aprove.verification.dpframework.Orders;

import java.util.logging.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.LimitPolynomials.*;
import aprove.xml.*;

/**
 *
 * Represents a LimitPolynomial order
 * @author kabasci
 *
 */
public class LimitPOLO implements QActiveOrder {

    public static Logger log = Logger.getLogger("LPOLO");


    private final LPOLSymbolRepresentations repres;
    private final LPOLInterpretor inter;

    /**
     * Create a LimitPOLO
     * @param repres The specialized representation of the symbols
     */
    public LimitPOLO(final LPOLSymbolRepresentations repres) {
        this.inter = new LPOLInterpretor(repres);
        this.repres = repres;
    }


    //TODO! We cannot handle QActive yet in LimitPOLO
    @Override
    public boolean checkQActiveCondition(final QActiveCondition condition) {
        // TODO Auto-generated method stub
        return false;
    }


    @Override
    public boolean areEquivalent(final TRSTerm s, final TRSTerm t) throws AbortionException {
        final LimitVarPolynomial p = this.inter.interpretTerm(s).minus(this.inter.interpretTerm(t));

        return p.geZero() && !p.gtZero();
    }

    @Override
    public boolean inRelation(final TRSTerm s, final TRSTerm t) throws AbortionException {

        if (this.inter.interpretTerm(s).minus(this.inter.interpretTerm(t)).gtZero()) {
            return true;
        } else {
            return false;
        }

    }

    @Override
    public boolean solves(final Constraint<TRSTerm> c) throws AbortionException {

        LimitPOLO.log.log(Level.FINEST, "Checking " + c.toString());

        final LimitVarPolynomial p = this.inter.interpretTerm(c.x).minus(this.inter.interpretTerm(c.y));
        LimitPOLO.log.log(Level.FINEST, "Interpretation " + p.toString());

        if (c.z == OrderRelation.EQ || c.z == OrderRelation.GENGR) {
            return !p.gtZero() && p.geZero();
        } else if (c.z == OrderRelation.GE) {
            return p.geZero();
        } else if (c.z == OrderRelation.GR) {
            return p.gtZero();
        } else if (c.z == OrderRelation.NGE) {
            return !p.geZero();
        } else {
            return false;
        }

    }

    @Override
    public String export(final Export_Util o) {
        return this.repres.export(o);
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        throw new RuntimeException("no CPF export " + this.isCPFSupported());
    }

    @Override
    public String isCPFSupported() {
        return this.getClass().getCanonicalName();
    }

}
