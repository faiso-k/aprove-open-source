package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import java.util.*;

/**
 * Generate simple alpha-numeric identifiers for variables.
 *
 * Generates identifiers of the form x<number>.
 */
public class SMTLIBVarMapper<V> {
    private final Map<V, String> nameMap;
    private int nameCount = 0;

    public SMTLIBVarMapper() {
        this.nameMap = new HashMap<V, String>();
    }

    /**
     * Get an identifier for var.
     */
    public String getName(V var) {
        String varName = this.nameMap.get(var);
        if (varName == null) {
            varName = "x" + this.nameCount++;
            this.nameMap.put(var, varName);
        }
        return varName;
    }

    /**
     * Returns the set of variables for which an identifier was generated.
     */
    public Set<V> getVariables() {
        return this.nameMap.keySet();
    }
}