package aprove.verification.oldframework.Algebra.Terms;

import java.util.*;

import aprove.verification.oldframework.Syntax.*;

/** This class implements the abstract FunctionApplication for the case
 *  of defined function applications.
 *  @author Burak Emir, Peter Schneider-Kamp
 *  @version $Id$
 */

public class DefFunctionApp extends AlgebraFunctionApplication {

    protected DefFunctionApp( DefFunctionSymbol sym, List<? extends AlgebraTerm> args) {
    super(sym, args);
    }

    /** Create a DefFunctionApp with zero arguments.
     */
    public static DefFunctionApp create(DefFunctionSymbol sym) {
    return DefFunctionApp.create(sym, new Vector<AlgebraTerm>());
    }

    /** Create a DefFunction from a symbol and an array of arguments.
     */
    public static DefFunctionApp create(DefFunctionSymbol sym, AlgebraTerm[] args) {
    AlgebraFunctionApplication.sanity_check(sym, args.length);
    Vector<AlgebraTerm> v = new Vector<AlgebraTerm>();
    for (int i=0; i<args.length; i++) {
        v.add(args[ i ]);
    };
    AlgebraFunctionApplication.sanity_check_args(v);
    return new DefFunctionApp(sym, v);
    }

    /** Creates a DefFunctionApp from a symbol and a list of terms.
     */
    public static DefFunctionApp create(DefFunctionSymbol sym, List<? extends AlgebraTerm> args) {
    AlgebraFunctionApplication.sanity_check( sym, args.size() );
    AlgebraFunctionApplication.sanity_check_args( args );
    return new DefFunctionApp(sym, args);
    }

    /** Hook for finely grained term visitors.
     *  @see FineGrainedTermVisitor
     */
    @Override
    final public <T> T apply(FineGrainedTermVisitor<T> ftv) {
    return ftv.caseDefFunctionApp(this);
    }

    public DefFunctionSymbol getDefFunctionSymbol() {
        return (DefFunctionSymbol)this.sym;
    }

    /** Very verbose representation of a constructor application. Mainly used for
     *  debugging purposes.
     */
    @Override
    public String verboseToString() {
    StringBuffer temp = new StringBuffer("{deffapp "+this.sym.getName()+"::");
    for (Iterator i = ((DefFunctionSymbol)this.sym).getArgSorts().iterator(); i.hasNext();) {
        temp.append(((Sort)i.next()).getName());
        if (i.hasNext()) {temp.append(", ");} else {temp.append(" -> ");}
    }
    temp.append(this.sym.getSort().getName()+" (");
    for (Iterator i = this.args.iterator(); i.hasNext();) {
        temp.append(((AlgebraTerm)i.next()).verboseToString());
        if (i.hasNext()) {
        temp.append(", ");
        }
    }
    temp.append(")}");
    return temp.toString();
    }

    @Override
    public boolean isTerminating() {
    if (!((DefFunctionSymbol)this.getSymbol()).getTermination()) {
        return false;
    }
    Iterator it = this.getArguments().iterator();
    while (it.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        if (!t.isTerminating()) {
        return false;
        }
    }
    return true;
    }

    @Override
    public boolean isConstructorTerm() {
        return false;
    }

    @Override
    public boolean isGroundTerm() {
        Iterator it = this.getArguments().iterator();
        while (it.hasNext()) {
            AlgebraTerm t = (AlgebraTerm)it.next();
            if (!t.isGroundTerm()) {
                return false;
            }
        }
        return true;
    }

    @Override
    final public boolean equals(Object o) {
        if(o instanceof DefFunctionApp) {
            DefFunctionApp t = (DefFunctionApp)o;
            return this.getSymbol().equals(t.getSymbol()) && this.args.equals(t.getArguments());
        }else{
            return false;
        }
    }
}
