package aprove.verification.dpframework.BasicStructures.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.Utility.*;


public class FreshVarGenerator {

    /**
     * The fresh name generator used internally.
     */
    protected FreshNameGenerator fng;

    public FreshVarGenerator() {
        this.fng = new FreshNameGenerator(new HashSet<String>(), FreshNameGenerator.VARIABLES);
    }

    public FreshVarGenerator(Collection<TRSVariable> usedVars) {
        this.fng = new FreshNameGenerator(this.namesFromVariables(usedVars), FreshNameGenerator.VARIABLES);
    }

    public FreshVarGenerator(FreshNameGenerator fng) {
        this.fng = fng;
    }

    public FreshVarGenerator(NameGenerator nameGen) {
        this(new FreshNameGenerator(nameGen));
    }

    private Set<String> namesFromVariables(Collection<TRSVariable> vars) {
        Set<String> names = new HashSet<String>();
        for (TRSVariable v : vars) {
            names.add(v.getName());
        }
        return names;
    }

    /**
     * Get a new variable given an old one.
     * @param v the old Variable.
     * @param useMemory True will cause subsequent calls to getFreshVariable with
     *        an equally-named variable to generate the same new-named variable.
     * @return A new variable.
     */
    public TRSVariable getFreshVariable(TRSVariable v, boolean useMemory) {
        String newName = this.fng.getFreshName(v.getName(), useMemory);
        return TRSTerm.createVariable(newName);
    }
}




