package aprove.verification.idpframework.Core.Utility;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

public class FreshVarGenerator {

    /**
     * The fresh name generator used internally.
     */
    protected final FreshNameGenerator fng;

    public FreshVarGenerator() {
        this.fng =
            new FreshNameGenerator(new HashSet<String>(),
                FreshNameGenerator.VARIABLES);
    }

    public FreshVarGenerator(final Collection<IVariable<?>> usedVars) {
        this.fng =
            new FreshNameGenerator(this.namesFromIVariables(usedVars),
                FreshNameGenerator.VARIABLES);
    }

    public FreshVarGenerator(final FreshNameGenerator fng) {
        this.fng = fng;
    }

    private synchronized Set<String> namesFromIVariables(final Collection<IVariable<?>> vars) {
        final Set<String> names = new HashSet<String>();
        for (final IVariable<?> v : vars) {
            names.add(v.getName());
        }
        return names;
    }

    /**
     * Get a new IVariable<?> given an old one.
     * @param v the old IVariable.
     * @param useMemory True will cause subsequent calls to getFreshIVariable<?>
     * with an equally-named IVariable<?> to generate the same new-named IVariable.
     * @return A new IVariable.
     */
    public synchronized <D extends SemiRing<D>> IVariable<D> getFreshVariable(final IVariable<D> v, final boolean useMemory) {
        final String newName = this.getFreshVariableName(v.getName(), useMemory);
        return ITerm.createVariable(newName, v.getDomain());
    }

    public synchronized <D extends SemiRing<D>> IVariable<D> getFreshVariable(final String name, final SemiRingDomain<D> domain, final boolean useMemory) {
        final String newName = this.getFreshVariableName(name, useMemory);
        return ITerm.createVariable(newName, domain);
    }

    public synchronized String getFreshVariableName(final String name, final boolean useMemory) {
        final String newName = this.fng.getFreshName(name, useMemory);
        return newName;
    }

    public synchronized boolean lockName(final String name) {
        return this.fng.lockName(name);
    }


    public synchronized boolean isUsed(final Set<? extends HasName> variableNames) {
        for (final HasName hasName : variableNames) {
            if (this.fng.isUnused(hasName.getName())) {
                return false;
            }
        }

        return true;
    }
}
