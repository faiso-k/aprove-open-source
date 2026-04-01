package aprove.verification.dpframework.Orders;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.xml.*;

public class AfsOrder implements QActiveOrder {

    private final Afs afs;
    private final ExportableOrder<TRSTerm> order;

    public AfsOrder(final Afs afs, final ExportableOrder<TRSTerm> order) {
        this.afs = afs;
        this.order = order;
    }

    @Override
    public boolean inRelation(final TRSTerm s, final TRSTerm t) throws AbortionException {
        return this.order.inRelation(this.afs.filterTerm(s), this.afs.filterTerm(t));
    }
    @Override
    public boolean solves(final Constraint<TRSTerm> c) throws AbortionException {
        return this.order.solves(Constraint.create(this.afs.filterTerm(c.x), this.afs.filterTerm(c.y), c.z));
    }

    @Override
    public boolean areEquivalent(final TRSTerm s, final TRSTerm t) throws AbortionException {
        return this.order.areEquivalent(this.afs.filterTerm(s), this.afs.filterTerm(t));
    }

    @Override
    public String export(final Export_Util o) {
        if (!this.afs.isFiltering()) {
            return this.order.export(o);
        }
        return "Combined order from the following AFS and order."+
        o.cond_linebreak()+this.afs.export(o)+o.cond_linebreak()+this.order.export(o);
    }

    @Override
    public boolean checkQActiveCondition(final QActiveCondition condition) {
        return condition.specialize(this.afs) == QActiveCondition.TRUE;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {

        if (this.isCPFSupported() != null) {
            throw new RuntimeException("please first ask isCPFSupported(): " + this.isCPFSupported());
        }
        final CPFExportableAfsOrder order = (CPFExportableAfsOrder) this.order;
        return order.toCPF(doc, xmlMetaData, this.afs.getFunctionSymbols(), this.afs);
    }

    @Override
    public String isCPFSupported() {
        final boolean support = this.order instanceof CPFExportableAfsOrder;
        return support ? null : "AFS + " + this.order.getClass().getCanonicalName();
    }


    @Override
    public String toString() {
        if (!this.afs.isFiltering()) {
            return this.order.toString();
        }
        return this.afs.toString()+"\n"+this.order.toString();
    }

    public Afs getAfs() {
        return this.afs;
    }

}
