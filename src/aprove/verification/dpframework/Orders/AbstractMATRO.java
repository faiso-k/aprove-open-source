package aprove.verification.dpframework.Orders;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Algebra.Matrices.*;
import aprove.verification.oldframework.Algebra.Matrices.Interpretation.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;


public abstract class AbstractMATRO implements QActiveOrder {

    private final SymbolRepresentations representation;
    private final ActiveResolver activeResolver;

    public AbstractMATRO(SymbolRepresentations representation, ActiveResolver activeResolver) {
        this.representation = representation;
        this.activeResolver = activeResolver;
    }

    @Override
    public boolean checkQActiveCondition(final QActiveCondition condition) {
        // we do NOT use return this.activeResolver.get(condition);
        // since this does not guarantee that usable rules are closed under right-hand sides
        Set<? extends Set<Pair<FunctionSymbol, Integer>>> dnf = condition.getSetRepresentation();
        nextDisjunct: for (Set<Pair<FunctionSymbol, Integer>> conjunction : dnf) {
            for (Pair<FunctionSymbol, Integer> fi : conjunction) {
                if (!this.representation.isActive(fi.x, fi.y)) {
                    continue nextDisjunct;
                }
            }
            return true;
        }
        return false;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return this.representation.toCPF(doc, xmlMetaData);
    }

    @Override
    public String export(final Export_Util o) {
        return this.representation.export(o)
            + (this.activeResolver.getActive()
                ? (o.newline() + "As matrix orders are CE-compatible, we used usable rules w.r.t. argument filtering in the order.")
                : "");
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String isCPFSupported() {
        return null;
    }

}
