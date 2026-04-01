package aprove.verification.oldframework.Algebra.Terms;

import java.io.*;
import java.util.*;

import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** Substitution of variables with terms. This class internally represents
 *  the substitution as a Hashtable mapping.
 * @author Peter Schneider-Kamp, Burak Emir
 * @version $Id$
 */

public class AlgebraSubstitution implements Serializable{

    protected  Map<VariableSymbol,AlgebraTerm> map;

    // ------------------- constructors

    protected  AlgebraSubstitution(Map<VariableSymbol,AlgebraTerm> map) {
    this.map = map;
    }

    public static AlgebraSubstitution create() {
    return new AlgebraSubstitution(new LinkedHashMap<VariableSymbol,AlgebraTerm>());
    }

    public static AlgebraSubstitution create(Map<VariableSymbol,AlgebraTerm> _map){
        return new AlgebraSubstitution(_map);
    }



    /** Returns the bindings corresponding to the variables in V.
     */
    public AlgebraSubstitution restrictTo(Set<AlgebraVariable> V) {
    Set<VariableSymbol> vsyms = new LinkedHashSet<VariableSymbol>();
    for(AlgebraVariable v : V ) {
        vsyms.add(v.getVariableSymbol());
    }
    AlgebraSubstitution res = AlgebraSubstitution.create();
    for( VariableSymbol sym : this.getDomain() ) {
        if(vsyms.contains(sym)) {
        res.put(sym, this.get(sym));
        }
    }

    return res;
    }

    // ---------------- accessor methods

    /** Returns the Term the given variable symbol is mapped to by this substitution.
     * @param vsym Variable symbol whose mapping should be returned.
     * @return Term that vsym maps to.
     */
    public AlgebraTerm get(VariableSymbol vsym) {
    return (AlgebraTerm)this.map.get(vsym);
    }

    /** Adds a new variable binding to this substitution.
     */
    public void put(VariableSymbol vsym, AlgebraTerm t) {
    this.map.put(vsym, t);
    }

    /** Removes a binding from this substitution.
     */
    public void remove(VariableSymbol vsym) {
    this.map.remove(vsym);
    }

    /** Return the underlying mapping of this substitution.
     */
    public Map<VariableSymbol,AlgebraTerm> getMapping() {
        return this.map;
    }

    /** Returns the domain of this substitution.
     */
    public Set<VariableSymbol> getDomain() {
    return new LinkedHashSet<VariableSymbol>(this.map.keySet());
    }

    /** Returns the domain of this substitution as variables.
     */
    public Set<AlgebraVariable> getTermDomain() {
    Set<VariableSymbol> symbs = new LinkedHashSet<VariableSymbol>(this.map.keySet());
    Set<AlgebraVariable> res = new LinkedHashSet<AlgebraVariable>();
    for(VariableSymbol variableSymbol : symbs) {
        res.add(AlgebraVariable.create(variableSymbol));
    }
    return res;
    }

    /** Returns the variables occuring in the range of this substitution.
     */
    public Set<AlgebraVariable> getRangeVariables() {
    Set<AlgebraVariable> res = new LinkedHashSet<AlgebraVariable>();
    for(AlgebraTerm term : this.map.values() ) {
        res.addAll(term.getVars());
    }
    return res;
    }

    /** Returns true if the given variable is contained in the
     *  domain of this substitution
     * @param vsym Variable symbol to check domain membership on.
     * @return True if vsym is contained in this substitution's domain
     */
    public boolean inDomain(VariableSymbol vsym) {
    return this.map.containsKey(vsym) && !this.map.get(vsym).getSymbol().equals(vsym);
    }

    /** Returns true if one the given variables is contained in the
     *  domain of this substitution
     * @param variableSymbols Variable symbosl to check domain membership on.
     * @return True if vsym is contained in this substitution's domain
     */
    public boolean inDomain(Collection<VariableSymbol> variableSymbols) {
        for(VariableSymbol variableSymbol : variableSymbols) {
            if(this.map.containsKey(variableSymbol) && !this.map.get(variableSymbol).getSymbol().equals(variableSymbol)) {
                return true;
            }
        }
        return false;
    }

    /** Returns true if the given term is contained in the
     *  range of this substitution
     * @param t Term to check range membership on.
     * @return True if vsym is contained in this substitution's domain
     */
    public boolean inRange(AlgebraTerm t) {
    return this.map.containsValue(t);
    }

    /** Composes this substitution with a given substitution.
     *  <p>
     *  This is implemented in such a way that
     *  <code>t.apply(p.compose(q)).equals(t.apply(p).apply(q))</code>
     *  for any term <code>t</code> and any substitutions <code>p</code>
     *  and <code>q</code>.
     * @param that Substitution to compose this subtitution with.
     * @return Substitution which is the composition of this
     *  subtitution with the given subtitution.
     */
    public AlgebraSubstitution compose(AlgebraSubstitution that) {
    AlgebraSubstitution sigma1 = AlgebraSubstitution.create();
    Iterator iKeys = this.getDomain().iterator();
    while(iKeys.hasNext()) {
        VariableSymbol var = (VariableSymbol)iKeys.next();
        sigma1.put(var, this.get(var).apply(that));
    }
    AlgebraSubstitution theta1 = AlgebraSubstitution.create();
    iKeys = that.getDomain().iterator();
    while(iKeys.hasNext()) {
        VariableSymbol var = (VariableSymbol)iKeys.next();
        if(!sigma1.getDomain().contains(var)) {
        theta1.put(var, that.get(var));
        }
    }
    AlgebraSubstitution sigma2 = AlgebraSubstitution.create();
    iKeys = sigma1.getDomain().iterator();
    while(iKeys.hasNext()) {
        VariableSymbol var = (VariableSymbol)iKeys.next();
        if(!sigma1.get(var).equals(AlgebraVariable.create(var))) {
        sigma2.put(var, sigma1.get(var));
        }
    }
    iKeys = theta1.getDomain().iterator();
    while(iKeys.hasNext()) {
        VariableSymbol var = (VariableSymbol)iKeys.next();
        sigma2.put(var, theta1.get(var));
    }
    return sigma2;
    }

    /** Makes a shallow copy of this substitution, i.e. of the
     *  underlying map. Neither the variable symbols nor the
     *  terms these map to are copied.
     */
    public AlgebraSubstitution shallowcopy() {
    return new AlgebraSubstitution(new LinkedHashMap<VariableSymbol,AlgebraTerm>(this.map));
    }

    /** Makes a deep copy of this substitution, i.e. of the
     *  underlying map. Both the variable symbols and the
     *  terms these map to are copied.
     */
    public AlgebraSubstitution deepcopy() {
    AlgebraSubstitution res = AlgebraSubstitution.create();
    Iterator i = this.map.keySet().iterator();
    while(i.hasNext()) {
        VariableSymbol v = (VariableSymbol)((VariableSymbol)i.next()).deepcopy();
        AlgebraTerm t = ((AlgebraTerm)this.map.get(v)).deepcopy();
        res.put(v, t);
    }
    return res;
    }

    /* Forbidden for security's and sanity's sake */
    @Override
    protected Object clone() {
    throw new RuntimeException("clone deprecated -- use deepcopy / shallowcopy instead");
    }

    //------------- miscellaneous methods

    /** Conversion to a string representation.
     */
    @Override
    public String toString() {
    StringBuffer temp = new StringBuffer("[");
    for (Iterator i=this.map.keySet().iterator(); i.hasNext();) {
        VariableSymbol var = (VariableSymbol)i.next();
        temp.append(var.getName()+"/"+this.map.get(var).toString());
        if (i.hasNext()) {
        temp.append(", ");
        }
    }
    temp.append("]");
    return temp.toString();
    }



    /** Test whether a substitution would fail the unfication algorithms occur check,
     *  e.g. {a/b, b/c } will return true.
     */
    public boolean failsOccurCheck(){
    boolean result = false;
    Iterator iKey = this.map.keySet().iterator();
    while (iKey.hasNext()) {
        VariableSymbol vsym = (VariableSymbol)iKey.next();
        AlgebraVariable var = AlgebraVariable.create(vsym);
        Iterator iElements = this.map.keySet().iterator();
        while (iElements.hasNext()) {
        VariableSymbol vsymCompare = (VariableSymbol)iElements.next();
        if (vsym!=vsymCompare) {
            AlgebraTerm t = (AlgebraTerm)this.map.get(vsymCompare);
            LinkedHashSet<AlgebraVariable> set = new LinkedHashSet<AlgebraVariable>(t.getVars());
            if (set.contains(var)) {
            return true;
            }
        }
        }
    }
    return result;
    }


    /** Test whether a substitution only renames variables, i.e. no variable is
     *  substitiuted by a functional or constructor term.
     */
    public boolean isVariableRenaming() {
    //go through Hashtable and check all the values whether they are all variables
    Iterator iElements = this.map.values().iterator();
    while (iElements.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)iElements.next();
        if (!(t instanceof AlgebraVariable)) {
        return false;
        }
    }
    return true;
    }

    @Override
    final public boolean equals(Object o) {
    AlgebraSubstitution s = (AlgebraSubstitution)o;
    return this.map.equals(s.getMapping());
    }

    @Override
    final public int hashCode() {
    return this.map.hashCode();
    }

    /** Extends a substitution by a second substitution. */
    public AlgebraSubstitution extend(AlgebraSubstitution sigma) {
    AlgebraSubstitution tau = this.shallowcopy();
    for(VariableSymbol vsym : sigma.getDomain() ){
        if (!this.inDomain(vsym)) {
        tau.put(vsym, sigma.get(vsym));
        }
    }
    return tau;
    }

    public boolean isNormal(Collection<Rule> rules) {
        for(AlgebraTerm t : this.map.values()){
            if (!t.isNormal(rules)) {
                return false;
            }
        }
        return true;
    }

    public boolean isConstructor() {
        for(AlgebraTerm t: this.map.values() ) {
            if (!t.getDefFunctionSymbols().isEmpty()) {
                return false;
            }
        }
        return true;
    }

    public Set<VariableSymbol> getVariableSymbolsInRange() {
        Set<VariableSymbol> result = new LinkedHashSet<VariableSymbol>();
        for(AlgebraTerm term : this.map.values() ) {
            result.addAll(term.getVariableSymbols());
        }
        return result;
    }
}
