package aprove.verification.oldframework.CostEquationSystem;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.WeightedIntTrs.*;

public class CostEquationSystem extends AbstractWeightedIntTermSystem<CostEquation> {

    public CostEquationSystem(String name, TRSFunctionApplication startTerm, Set<CostEquation> equations) {
        super("CES","CostEquationSystem", name, equations, startTerm);
    }

    @Override
    public CostEquationSystem copyWithNewRules (Collection<CostEquation> newRules) {
        return new CostEquationSystem(this.name, this.startTerm, new LinkedHashSet<>(newRules));
    }

    @Override
    public AbstractWeightedIntTermSystem<CostEquation> copyWithNewRules(Collection<CostEquation> newRules, TRSFunctionApplication newStartTerm) {
        return new CostEquationSystem(this.name, newStartTerm, new LinkedHashSet<>(newRules));
    }

    @Override
    public String getStrategyName() {
        return "CESBackend";
    }

    @Override
    public String export(Export_Util eu) {
        String res = eu.escape("CostEquationSystem with " + rules.size() + " equations");
        res += eu.newline();
        res += eu.escape("Start term: ");
        res += startTerm.export(eu);
        res += eu.newline();
        res += eu.escape("Equations:");
        res += eu.newline();
        for (CostEquation e: rules) {
            res += e.export(eu) + eu.newline();
        }
        return res;
    }

    @Override
    public String toString() {
        return export(new PLAIN_Util());
    }

}
