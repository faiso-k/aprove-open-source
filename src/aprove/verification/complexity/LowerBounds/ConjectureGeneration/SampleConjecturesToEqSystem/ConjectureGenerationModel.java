package aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem;

import java.math.*;
import java.util.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.BasicStructures.*;

/**
 * When we convert narrowing sequences to linear equation systems, then we get multiple models,
 * namely one for each integer-typed RulePosition. This is the container for these models.
 */
public class ConjectureGenerationModel {

    private Map<RulePosition, Map<String, BigInteger>> theModels = new LinkedHashMap<>();

    public void setModel(RulePosition pos, Map<String, BigInteger> modelForPos) {
        this.theModels.put(pos, modelForPos);
    }

    public Map<String, BigInteger> getModel(RulePosition pos) {
        return this.theModels.get(pos);
    }

    public Set<RulePosition> positions() {
        return this.theModels.keySet();
    }

    /** Convert the model for the linear equation system for the given position to a term. */
    public TRSTerm toTerm(RulePosition pos, LowerBoundsToolbox toolbox) {
        Map<String, BigInteger> aModel = this.theModels.get(pos);
        TRSTerm res = null;
        for (String coefficient: aModel.keySet()) {
            int degree = Integer.parseInt(coefficient.substring(1));
            TRSTerm subRes = PFHelper.toTerm(aModel.get(coefficient));
            for (int i=0; i<degree; i++) {
                subRes = TRSTerm.createFunctionApplication(PFHelper.MUL, subRes, toolbox.inductionVar);
            }
            if (res == null) {
                res = subRes;
            } else {
                res = TRSTerm.createFunctionApplication(PFHelper.ADD, res, subRes);
            }
        }
        return res;
    }

    /**
     * Create a new instance representing the same model like this one, but with domain newDomain,
     * where all new coefficients are zero. Useful to compare models with different domains.
     */
    public ConjectureGenerationModel extendVanishing(Set<String> newDomain) {
        ConjectureGenerationModel clone = this.clone();
        for (Map<String, BigInteger> model : clone.theModels.values()) {
            Set<String> oldDomain = model.keySet();
            for (String var : newDomain) {
                if (!oldDomain.contains(var)) {
                    model.put(var, BigInteger.ZERO);
                }
            }
        }
        return clone;
    }

    @Override
    public ConjectureGenerationModel clone() {
        ConjectureGenerationModel res = new ConjectureGenerationModel();
        for (RulePosition pos: this.theModels.keySet()) {
            res.theModels.put(pos, new LinkedHashMap<>(this.theModels.get(pos)));
        }
        return res;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.theModels == null) ? 0 : this.theModels.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        ConjectureGenerationModel other = (ConjectureGenerationModel) obj;
        if (this.theModels == null) {
            if (other.theModels != null) {
                return false;
            }
        } else if (!this.theModels.equals(other.theModels)) {
            return false;
        }
        return true;
    }

    public boolean equalsExtendVanishing(ConjectureGenerationModel that) {
        Set<String> domain = this.getDomain();
        ConjectureGenerationModel extendedModel = that.extendVanishing(domain);
        return this.equals(extendedModel);
    }

    private Set<String> getDomain() {
        assert !this.theModels.isEmpty();
        return this.theModels.values().iterator().next().keySet();
    }
}
