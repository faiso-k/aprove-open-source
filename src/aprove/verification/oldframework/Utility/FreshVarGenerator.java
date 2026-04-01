package aprove.verification.oldframework.Utility;

import java.util.*;

import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Generator for fresh variables that uses FreshNameGenerator internally.
 * @author Burak Emir, Carsten Pelikan, Peter Schneider-Kamp
 * @version $Id$
 */

public class FreshVarGenerator {

    /** The fresh name generator used internally.*/
    protected FreshNameGenerator fng;

    public FreshVarGenerator(Collection<AlgebraVariable> usedVars, NameGenerator mode) {
        this.fng = new FreshNameGenerator(this.namesFromVariables(usedVars), mode);
    }

    public FreshVarGenerator() {
        this.fng = new FreshNameGenerator(new HashSet<String>(), FreshNameGenerator.VARIABLES);
    }

    public FreshVarGenerator(Collection<AlgebraVariable> usedVars) {
        this.fng = new FreshNameGenerator(this.namesFromVariables(usedVars), FreshNameGenerator.VARIABLES);
    }

    public FreshVarGenerator(AlgebraTerm t) {
        this.fng = new FreshNameGenerator(this.namesFromVariables(t.getVars()), FreshNameGenerator.VARIABLES);
    }

    public Set getUsedVariableNames() {
        return this.fng.getUsedNames();
    }

    private Set<String> namesFromVariables(Collection<AlgebraVariable> vars) {
        Set<String> names = new HashSet<String>();
        Iterator i = vars.iterator();
        while (i.hasNext()) {
            AlgebraVariable var = (AlgebraVariable)i.next();
            names.add(var.getName());
        }
        return names;
    }

    /** Get a new variable given an old one.
     * @param v the old Variable.
     * @param useMemory True will cause subsequent calls to getFreshVariable with
     *        an equally-named variable to generate the same new-named variable.
     * @return A new variable.
     */
    public AlgebraVariable getFreshVariable(AlgebraVariable v, boolean useMemory) {
        String newName = this.fng.getFreshName(v.getName(), useMemory);
        return AlgebraVariable.create(VariableSymbol.create(newName, v.getSort()));
    }

    /** Create a new variable with a given sort starting with a certain string.
     * @param start The string to start the variable's name with.
     * @param sort The sort of the new variable.
     * @param useMemory True will cause subsequent calls to getFreshVariable with
     *        an equally-named variable to generate the same new-named variable.
     * @return A new variable of the given sort.
     */
    public AlgebraVariable getFreshVariable(String start, Sort sort, boolean useMemory) {
        String newName = this.fng.getFreshName(start, useMemory);
        return AlgebraVariable.create(VariableSymbol.create(newName, sort));
    }

    public FreshVarGenerator shallowcopy() {
    FreshVarGenerator res = new FreshVarGenerator();
    res.fng = this.fng.shallowcopy();
    return res;
    }

}
