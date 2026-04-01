package aprove.verification.oldframework.Syntax;

/* Implementation of a defined function symbol.
 * <p>
 * Note: The rules defining this symbol are no longer stored inside this symbol.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Utility.*;

public class DefFunctionSymbol extends SyntacticFunctionSymbol implements Checkable {

    protected boolean termination;

    /** The signature-class this symbol is in.  */
    protected int signatureClass = Symbol.DEFAULTSIG;

    /** Stores the jCommutativity of the function symbol. */
    protected Boolean[] jCommutativity = null;

    /* constructors */

    protected DefFunctionSymbol(String name, List<Sort> argsorts, Sort sort) {
        super(name, argsorts, sort);
        this.termination = false;
    }

    protected DefFunctionSymbol(String name, int arity) {
        super(name,arity);
        this.termination = false;
    }

    public static DefFunctionSymbol create(String name, int arity) {
        return new DefFunctionSymbol(name,arity);
    }

    public static DefFunctionSymbol create(String name, int arity, int fixity) {
        DefFunctionSymbol defunctionSymbol = new DefFunctionSymbol(name,arity);
        defunctionSymbol.setFixity(fixity);
        return defunctionSymbol;
    }

    public static DefFunctionSymbol create(String name, List<Sort> argsorts, Sort sort) {
    return new DefFunctionSymbol(name, argsorts, sort);
    }

    public static DefFunctionSymbol create(String name, int arity, Sort sort) {
    return DefFunctionSymbol.create(name, arity, sort, sort);
    }

    public static DefFunctionSymbol create(String name, int arity, Sort argSort, Sort sort) {
        return new DefFunctionSymbol(name, Sort.getVectorOfStandardSort(arity,argSort), sort);
    }

    /** Allows FineSymbolVisitor objects to visit this object.
     */
    @Override
    public Object apply(FineSymbolVisitor fsv) {
    return fsv.caseDefFunctionSymbol(this);
    }

    /* accessors */

    /** Get the rules for this defined function symbol.
     */
    public Set<Rule> getBody(Program prog) {
    return prog.getRules(this);
    }

    /** Add a rule to this defined function symbol's body.
     */
    public void addRule(Program prog, Rule rule) {
    prog.addRule(this, rule);
    }

    /** Set the termination status of this defined function.
     *  <p>
     *  Note: Just set this to true if you know this function terminates (e.g. by construction).
     */
    public void setTermination(boolean termination) {
    this.termination = termination;
    }

    /** Get the termination status of this defined function.
     *  <p>
     *  Note: false means termination status is UNKNOWN
     */
    public boolean getTermination() {
    return this.termination;
    }

    @Override
    public String toString() {
        return super.toString();
    }

    public String toString(Program prog) {
    StringBuffer temp = new StringBuffer(super.toString()+" [\n");
    for (Iterator i = prog.getRules(this).iterator(); i.hasNext();) {
        temp.append("  "+((Rule)i.next()).toString());
        if (i.hasNext()) {
            temp.append("\n");
        }
    }
    for(Iterator i = prog.getEquations(this).iterator(); i.hasNext();) {
        temp.append("\n  "+((TRSEquation)i.next()).toString());
    }
        temp.append("\n]\n");
    return temp.toString();
    }

    @Override
    public String verboseToString() {
    StringBuffer temp = new StringBuffer("{deff "+this.name+"::");
    for (Iterator i = this.argSorts.iterator(); i.hasNext();) {
        temp.append(((Sort)i.next()).getName());
        if (i.hasNext()) {temp.append(", ");} else {temp.append(" -> ");}
    }
    return temp.toString()+"}\n";
    }

    public String verboseToString(Program prog) {
    StringBuffer temp = new StringBuffer("{deff "+this.name+"::");
    for (Iterator i = this.argSorts.iterator(); i.hasNext();) {
        temp.append(((Sort)i.next()).getName());
        if (i.hasNext()) {temp.append(", ");} else {temp.append(" -> ");}
    }
    temp.append(this.sort.getName()+" :=\n");
    for (Iterator i = prog.getRules(this).iterator(); i.hasNext();) {
        temp.append(((Rule)i.next()).verboseToString());
        if (i.hasNext()) {
            temp.append("\n");
        }
    }
    return temp.toString()+"}\n";
    }

    public Set<Position> getAlterablePositions(Program prog) {
    Set<Position> result = new HashSet<Position>();
    if (!this.isRecursive(prog)) {
        return result;
    }
    Iterator iRule = prog.getRules(this).iterator();
    while (iRule.hasNext()) {
        Rule rule = (Rule)iRule.next();
        AlgebraFunctionApplication left = (AlgebraFunctionApplication)rule.getLeft();
        List<AlgebraTerm> leftArgsPattern = left.getArguments();
        Set<Position> pos = rule.getRight().getPositionsWithSymbol(this);
        Iterator iPos= pos.iterator();
        while (iPos.hasNext()) {
        Position p = (Position)iPos.next();
        AlgebraFunctionApplication right = (AlgebraFunctionApplication)rule.getRight().getSubterm(p);
        List<AlgebraTerm> rightArgsPattern = right.getArguments();
        //check if all positions are the same
        for (int i=0; i<this.getArity(); i++) {
            AlgebraTerm s = (AlgebraTerm)leftArgsPattern.get(i);
            AlgebraTerm t = (AlgebraTerm)rightArgsPattern.get(i);
            if (!s.equals(t)) {
            Position alterablePos = Position.create();
            alterablePos.add(i);
            result.add(alterablePos);
            }//endif
        }//for pos
        }//for recursive pos
    }//for rules
    return result;
    }

    /** Returns all vars used in all rules.
     */
    public Set<AlgebraVariable> getUsedVariables(Program prog) {
    HashSet<AlgebraVariable> result = new HashSet<AlgebraVariable>();
    Iterator iRule = prog.getRules(this).iterator();
    while (iRule.hasNext()) {
        Rule rule = (Rule)iRule.next();
        result.addAll(rule.getUsedVariables());
    }
    return result;
    }

    public Object shallowcopy() {
    DefFunctionSymbol fsym = new DefFunctionSymbol(this.name, this.argSorts, this.sort);
    fsym.setTermination(this.getTermination());
        fsym.setFixity(this.getFixity(), this.getFixityLevel());
    return fsym;
    }

    @Override
    public Symbol deepcopy() {

        if(this.argSorts != null) {

            Vector<Sort> v1 = new Vector<Sort>();
            Iterator i = this.argSorts.iterator();
            while (i.hasNext()) {
                v1.add((Sort)i.next());
            }


            DefFunctionSymbol fsym = new DefFunctionSymbol(this.name, v1, this.sort);

            fsym.setTermination(this.getTermination());
            fsym.setFixity(this.getFixity(), this.getFixityLevel());
            return fsym;
        }

        DefFunctionSymbol fsym = new DefFunctionSymbol(this.name, this.getArity());
        return fsym;
    }

    /** Returns the signature-class to which this function symbol belongs. */
    @Override
    public int getSignatureClass() {
    return this.signatureClass;
    }

    /** Sets the signature-class to which this function symbol belongs. */
    public void setSignatureClass(int sc) {
    this.signatureClass = sc;
    }

    /** Returns whether this function is j-commutative.
     *  @param j Position of commutativity.
     *  @return true, if function is j-commutative, false if j-commutativity
     *  could not be shown, null if there was no attempt to check
     *  j-commutativity, yet. */
    public Boolean isJCommutative(int j) {
    if (this.jCommutativity == null) {
        return null;
    }
    return this.jCommutativity[j];
    }

    /** Set whether this function is j-commutative. */
    public void setJCommutativity(int j, Boolean b) {
    if (this.jCommutativity == null) {
        this.jCommutativity = new Boolean[this.getArity()];
    }
    this.jCommutativity[j] = b;
    }

    /** Sets every position from "unknown" (false) to "not tried" (null).
     */
    public void resetUnknownJCommutativity() {
    if (this.jCommutativity != null) {
        for (int i=this.getArity()-1; i>=0; i--) {
        Boolean b = this.jCommutativity[i];
        if (b != null && !b.booleanValue()) {
            this.jCommutativity[i] = null;
        }
        }
    }
    }

}
