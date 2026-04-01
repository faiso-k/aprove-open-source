package aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem;

import java.util.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;


public class LinearEqSystemMap {

    private Map<RulePosition, LinearEqSystem> systems = new LinkedHashMap<>();

    public void addAll(Map<RulePosition, LinearEqSystem> toAdd) {
        for (RulePosition pos : toAdd.keySet()) {
            if (this.systems.containsKey(pos)) {
                this.systems.put(pos, toAdd.get(pos).and(this.systems.get(pos)));
            } else {
                this.systems.put(pos, toAdd.get(pos));
            }
        }
    }

    public Set<RulePosition> keySet() {
        return this.systems.keySet();
    }

    public LinearEqSystem get(RulePosition pos) {
        return this.systems.get(pos);
    }
}
