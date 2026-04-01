package aprove.verification.oldframework.Algebra.Terms;

import java.util.*;

import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.LemmaDatabase.Index.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/** This class represents a term consisting of just a variable. Variable terms
 *  can be renamed by calling the rename method with a new variable symbol.
 * @author Burak Emir
 * @version $Id$
 */

public class AlgebraVariable extends AlgebraTerm {

    /** Returns the name of this variable's symbol.
     */
    public String getName() {
    return this.sym.getName();
    }

    /** Returns the symbol of this variable.
     */
    public VariableSymbol getVariableSymbol() {
    return (VariableSymbol)this.sym;
    }

    protected AlgebraVariable(VariableSymbol sym) {
    this.sym = sym;
    }

    @Override
    final public boolean equals(Object o) {

    if( o == null || !(o instanceof AlgebraVariable)) {
        return false;
    }

    AlgebraTerm t = (AlgebraTerm)o;
    return t.isVariable() && this.getSymbol().equals(t.getSymbol());
    }

    @Override
    final public int hashCode() {
    return this.toString().hashCode();
    }

    /** Always returns true.
    */
    @Override
    final public boolean isVariable() {
    return true;
    }

    /** Always returns null as there cannot be arguments.
     */
    @Override
    final public List<AlgebraTerm> getArguments() {
    return null;
    }

    /** Always throws an UnsupportedOperationException.
     */
    @Override
    public AlgebraTerm getArgument(int index) {
    throw new UnsupportedOperationException();
    }

    /** Rename this variable term using a new variable symbol.
     */
    public void rename(VariableSymbol sym) {
    this.sym = sym;
    }

    /** Rename this variable using a String - the String is captured.
     */
    public void rename(String s) {
    this.sym = VariableSymbol.create(s, this.sym.getSort());
    }

    /** Public constructor specifying name and sort.
     */
    public static AlgebraVariable create(VariableSymbol sym) {
    return new AlgebraVariable(sym);
    }

    @Override
    public AlgebraTerm createWithFriendlyNames(FreshNameGenerator ngen, Program prog) {
    Sort s = prog.getSort(ngen.getFreshName(this.getSymbol().getSort().getName(),true));
    if (s == null) {
        return null;
    }
    return AlgebraVariable.create(VariableSymbol.create(ngen.getFreshName(this.getSymbol().getName(),true),s));
    }

    /** Hook for coarsely grained term visitors.
     */
    @Override
    final public <T> T apply(CoarseGrainedTermVisitor<T> ctv) {
    return ctv.caseVariable(this);
    }

    /** Hook for finely grained term visitors.
     */
    @Override
    final public <T> T apply(FineGrainedTermVisitor<T> ftv) {
    return ftv.caseVariable(this);
    }


    @Override
    public <T> T apply(CoarseGrainedTermVisitorException<T> ctve)
            throws InvalidPositionException {
        return ctve.caseVariable(this);
    }

    /** Very verbose representation of a constructor application. Mainly used for
     *  debugging purposes.
     */
    @Override
    public String verboseToString() {
    return "{varterm "+this.sym.verboseToString()+"}";
    }

    @Override
    public AlgebraTerm shallowcopy() {
    AlgebraTerm t = new AlgebraVariable((VariableSymbol)this.sym);
    t.setAttributes(this.getAttributes());
    return t;
    }

    @Override
    public AlgebraTerm deepcopy() {
        AlgebraTerm t = new AlgebraVariable((VariableSymbol) this.sym);
        Hashtable<String, Object> attr = this.getAttributes();
        if (attr != null) {
            Hashtable<String, Object> newattr = new Hashtable<String, Object>(
                    attr);
            Hashtable<String, Integer> label = (Hashtable<String, Integer>) attr
                    .get("label");
            if (label != null) {
                newattr.put("label", new Hashtable<String, Integer>(label));
            }
            t.setAttributes(newattr);
        }
        return t;
    }

/*    public Term paranoidcopy() {
    return new Variable((VariableSymbol)this.sym.deepcopy());
    }*/

    @Override
    public boolean isTerminating() {
    return true;
    }

    @Override
    public int size() {
    return 1;
    }

    @Override
    public boolean isConstructorTerm() {
        return true;
    }

    @Override
    public boolean isGroundTerm() {
        return false;
    }

    @Override
    public int width() {
        return 0;
    }

    @Override
    public aprove.verification.dpframework.BasicStructures.TRSTerm toNewTerm() {
        return aprove.verification.dpframework.BasicStructures.TRSTerm.createVariable(this.getName());
    }

    @Override
    public IndexSymbol getRootIndexSymbol() {
        return new IndexVariableSymbol();
    }
}
