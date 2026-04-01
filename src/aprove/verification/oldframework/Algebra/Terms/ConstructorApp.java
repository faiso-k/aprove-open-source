package aprove.verification.oldframework.Algebra.Terms;

import java.util.*;

import aprove.verification.oldframework.Syntax.*;

/** This class implements the abstract FunctionApplication for the case
 *  of constructor applications.
 *  @author Burak Emir, Peter Schneider-Kamp
 *  @version $Id$
 */

public class ConstructorApp extends AlgebraFunctionApplication {

    protected ConstructorApp(ConstructorSymbol sym, List<? extends AlgebraTerm> args) {
    super(sym, args);
    }

    /** Creates a ConstructorApp with an empty list of arguments.
     */
    public static ConstructorApp create(ConstructorSymbol sym) {
    return ConstructorApp.create( sym, new Vector<AlgebraTerm>() );
    }

    /** Creates a ConstructorApp from a symbol and an array of arguments.
     */
    public static ConstructorApp create(ConstructorSymbol sym, AlgebraTerm[] args) {
    AlgebraFunctionApplication.sanity_check(sym, args.length);
    Vector<AlgebraTerm> v = new Vector<AlgebraTerm>();
    for (int i=0; i<args.length; i++) {
        v.add(args[ i ]);
    };
    AlgebraFunctionApplication.sanity_check_args(v);
    return new ConstructorApp(sym, v);
    }

    /** Creates a ConstructorApp from a symbol and a list of arguments.
     */
    public static ConstructorApp create(ConstructorSymbol sym, List<? extends AlgebraTerm> args) {
    AlgebraFunctionApplication.sanity_check(sym, args.size());
    AlgebraFunctionApplication.sanity_check_args(args);
    return new ConstructorApp(sym, args);
    }

    /** Hook for finely grained term visitors.
     *  @see FineGrainedTermVisitor
     */
    @Override
    final public <T> T apply(FineGrainedTermVisitor<T> ftv) {
    return ftv.caseConstructorApp(this);
    }

    /** Very verbose representation of a constructor application. Mainly used for
     *  debugging purposes.
     */
    @Override
    public String verboseToString() {
    StringBuffer temp = new StringBuffer("{consapp "+this.sym.verboseToString()+" (");
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
        Iterator it = this.getArguments().iterator();
        while (it.hasNext()) {
            AlgebraTerm t = (AlgebraTerm)it.next();
            if (!t.isConstructorTerm()) {
                return false;
            }
        }
        return true;
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

        if(o instanceof ConstructorApp) {
            ConstructorApp t = (ConstructorApp)o;
            return this.getSymbol().equals(t.getSymbol()) && this.args.equals(t.getArguments());
        }else{
            return false;
        }
    }

    public ConstructorSymbol getConstructorSymbol() {
        return (ConstructorSymbol)this.sym;
    }
}
