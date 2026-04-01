package aprove.verification.oldframework.Algebra.Terms;

import java.io.*;
import java.util.*;

import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.LemmaDatabase.Index.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/** This class represents terms that are the result of an application of a function to
 *  a list of arguments.
 *  @author Burak Emir
 *  @version $Id$
 */

public abstract class AlgebraFunctionApplication extends AlgebraTerm {

    protected List<AlgebraTerm> args;

    public SyntacticFunctionSymbol getFunctionSymbol() {
    return (SyntacticFunctionSymbol)this.sym;
    }

        public static AlgebraFunctionApplication createWithDisjointVars(SyntacticFunctionSymbol sym) {
            int i = 0;
            List<AlgebraTerm> args = new ArrayList<AlgebraTerm>();
            Iterator it = sym.getArgSorts().listIterator();
            while (it.hasNext()) {
                Sort s = (Sort) it.next();
                i = i + 1;
                VariableSymbol varSym = VariableSymbol.create("x_"+i,s);
                args.add(AlgebraVariable.create(varSym));
            }
            if (sym instanceof DefFunctionSymbol) {
                return (DefFunctionApp.create((DefFunctionSymbol) sym,args));
            }
            if (sym instanceof ConstructorSymbol) {
                return (ConstructorApp.create((ConstructorSymbol) sym,args));
            }
            return null;
        }
    public static AlgebraFunctionApplication createWithDisjointVars(SyntacticFunctionSymbol sym, FreshNameGenerator namegen) {
    int i = 0;
    List<AlgebraTerm> args = new ArrayList<AlgebraTerm>();
    Iterator it = sym.getArgSorts().listIterator();
    while (it.hasNext()) {
        Sort s = (Sort) it.next();
        i = i + 1;
        String name = namegen.getFreshName("x_"+i, false);
        VariableSymbol varSym = VariableSymbol.create(name, s);
        args.add(AlgebraVariable.create(varSym));
    }
    if (sym instanceof DefFunctionSymbol) {
        return (DefFunctionApp.create((DefFunctionSymbol) sym,args));
    }
    if (sym instanceof ConstructorSymbol) {
        return (ConstructorApp.create((ConstructorSymbol) sym,args));
    }
    return null;
    }

    public static AlgebraFunctionApplication createWithDisjointVars(SyntacticFunctionSymbol sym, FreshVarGenerator namegen) {
        int i = 0;
        List<AlgebraTerm> args = new ArrayList<AlgebraTerm>();
        Iterator it = sym.getArgSorts().listIterator();
        while (it.hasNext()) {
            Sort s = (Sort) it.next();
            i = i + 1;
            AlgebraVariable variable = namegen.getFreshVariable("x_"+i, s, false);
            args.add(variable);
        }
        if (sym instanceof DefFunctionSymbol) {
            return (DefFunctionApp.create((DefFunctionSymbol) sym,args));
        }
        if (sym instanceof ConstructorSymbol) {
            return (ConstructorApp.create((ConstructorSymbol) sym,args));
        }
        return null;
        }

    protected AlgebraFunctionApplication(SyntacticFunctionSymbol sym, List<? extends AlgebraTerm> args) {
    this.sym = sym;
    this.args = new ArrayList<AlgebraTerm>(args);
    }

    @Override
    final public int hashCode() {
    return this.toString().hashCode();
    }

    /** Returns the arguments of this function. Changing the list affects this term.
     */
    @Override
    final public List<AlgebraTerm> getArguments() {
    return this.args;
    }

    /** Creates a 0-ary function symbol.
     */
    public static AlgebraFunctionApplication create(final SyntacticFunctionSymbol sym) {
    return AlgebraFunctionApplication.create(sym, new ArrayList<AlgebraTerm>());
    }

    /** Creates a FunctionApplication of a symbol and a list of arguments.
     *  <p>
     *  Note: This method calls create(FunctionSymbol, List<? extends Term>)
     *  and by this the create methods of the appropriate
     *  subclass in order to create a new object are called.
     */
    public static AlgebraFunctionApplication create(final SyntacticFunctionSymbol sym, final AlgebraTerm[] args) {
        Vector<AlgebraTerm> v = new Vector<AlgebraTerm>(args.length);
        for (int i=0; i<args.length; i++) {
            v.add(args[ i ]);
        }
        return AlgebraFunctionApplication.create(sym, v);
    }


    /** Creates a FunctionApplication of a symbol and a list of arguments.
     *  <p>
     *  Note: This method calls the create methods of the appropriate
     *  subclass in order to create a new object.
     */
    public static AlgebraFunctionApplication create(final SyntacticFunctionSymbol sym, final List<? extends AlgebraTerm> args) {
    AlgebraFunctionApplication.sanity_check(sym, args.size());
    AlgebraFunctionApplication.sanity_check_args(args);
    return (AlgebraFunctionApplication)sym.apply(new FineSymbolVisitor() {
        @Override
        public Object caseVariableSymbol(VariableSymbol sym) {
        return null; // should never happen
        }
        @Override
        public Object caseConstructorSymbol(ConstructorSymbol sym) {
        return ConstructorApp.create(sym, args);
        }
        @Override
        public Object caseDefFunctionSymbol(DefFunctionSymbol sym) {
        return DefFunctionApp.create(sym, args);
        }
        @Override
        public Object caseMetaFunctionSymbol(MetaFunctionSymbol msym) {
            return MetaFunctionApplication.create(msym,args);
        }

    });
    }

    @Override
    public AlgebraTerm createWithFriendlyNames(FreshNameGenerator ngen, Program prog) {
    List<AlgebraTerm> newargs = new ArrayList<AlgebraTerm>();
    Iterator it = this.args.iterator();
    while (it.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        AlgebraTerm ta = t.createWithFriendlyNames(ngen, prog);
        if (ta == null) {
            return null;
        }
        newargs.add(ta);
    }
    SyntacticFunctionSymbol sym = prog.getFunctionSymbol(ngen.getFreshName(this.getSymbol().getName(), true));
    return AlgebraFunctionApplication.create(sym, newargs);
    }

    /** Sanity check for constructing a function application.
     */
    protected static void sanity_check(SyntacticFunctionSymbol sym, int nargs ) {
    if (sym==null) {
        throw new IllegalArgumentException("symbol == null, could not create FunctionApplication");
    }
    if (sym.getArity() != nargs) {
        throw new IllegalArgumentException(sym.getName()+" expects "+sym.getArity()+" arguments, "+nargs+"given.\n"+sym.toString());
    }
    }

    /** Checks if all arguments are != null.
     */
    protected static void sanity_check_args(List<? extends AlgebraTerm> args) {
    for (Iterator i = args.iterator(); i.hasNext();) {
        AlgebraTerm s = (AlgebraTerm)i.next();
        if (s == null) {
            throw new IllegalArgumentException("encountered an argument equal to null");
        }
    }
    }

    /** Returns the i-th argument of this FunctionApplication.
     */
    @Override
    final public AlgebraTerm getArgument(int index) {
    return (AlgebraTerm)this.args.get(index);
    }

    /** Replaces the i-th argument of this FunctionApplication.
     * Method by azazel: Be carefull, I'm not sure if this can be done without sideeffects. Maybe someone
     * will remove this line of comment, if he or she knows that this will work allright.
     */
    public void replaceArgument(int index, AlgebraTerm newArgument) {
    this.args.set(index, newArgument);
    };

    /** Always returns false.
     */
    @Override
    final public boolean isVariable() {
    return false;
    }

    /** Hook for coarsely grained term visitors.
     */
    @Override
    final public <T> T apply(CoarseGrainedTermVisitor<T> ctv) {
    return ctv.caseFunctionApp(this);
    }

    @Override
    public <T> T apply(CoarseGrainedTermVisitorException<T> ctv)
        throws InvalidPositionException{
        return ctv.caseFunctionApp(this);
    }
    @Override
    public AlgebraTerm shallowcopy() {
    AlgebraTerm t = AlgebraFunctionApplication.create((SyntacticFunctionSymbol)this.sym, this.args);
    t.setAttributes(this.getAttributes());
    return t;
    }

    @Override
    public AlgebraTerm deepcopy() {
    ArrayList<AlgebraTerm> v = new ArrayList<AlgebraTerm>();
    Iterator i = this.args.iterator();
    while (i.hasNext()) {
        v.add(((AlgebraTerm)i.next()).deepcopy());
    }
    AlgebraTerm t = AlgebraFunctionApplication.create((SyntacticFunctionSymbol)this.sym, v);
    Hashtable<String,Object> attr = this.getAttributes();
    if (attr != null) {
        Hashtable<String,Object> newattr = new Hashtable<String,Object>(attr);
        Hashtable<String,Integer> label = (Hashtable<String,Integer>)attr.get("label");
        if (label != null) {
        newattr.put("label", new Hashtable<String,Integer>(label));
        }
        t.setAttributes(newattr);
    }

    return t;
    }

/*    public Term paranoidcopy() {
    ArrayList<Term> v = new ArrayList<Term>();
    Iterator i = this.args.iterator();
    while (i.hasNext()) {
        v.add(((Term)i.next()).paranoidcopy());
    }
    return FunctionApplication.create((FunctionSymbol)this.sym.deepcopy(), v);
    }*/

    /**
     * This method can influence the object input stream in the sense that post operations can be done.
     * In this case, the refernce of a term symbol is set
     * @param in is the  object input stream it recieves
     * @throws IOException
     * @throws ClassNotFoundException
     */
    private void readObject(ObjectInputStream in) throws IOException, ClassNotFoundException{
        in.defaultReadObject();
        try{
             InputStreamWithProg s = (InputStreamWithProg)in;
             Program p =s.getProgram();
             Symbol symFromProg = p.getFunctionSymbol(this.sym.getName());
             this.sym = symFromProg;
        }
        catch (ClassCastException cxExp){
        }
    }

    @Override
    public int size() {
    int n = 1;
    Iterator it = this.getArguments().iterator();
    while (it.hasNext()) {
        n += ((AlgebraTerm)it.next()).size();
    }
    return n;
    }

    /** rearranges infix operators within the term so that they respect their fixity level.
     *
     * Example: (a + b) * c will become a + (b * c) if no paranthesis flag protectes the
     * (a + b) term. To set this flag add the tuple ("FLAG_PARANTHESIS", true) into the
     * attributes map
     *
     * Method is still under construction!! Don't rely on it! (azazel, 25.04.2004)
     */
    public AlgebraTerm rearrangeByFixity() {
    SyntacticFunctionSymbol sym = (SyntacticFunctionSymbol) this.getSymbol();
    if (sym.getFixity() == SyntacticFunctionSymbol.NOTINFIX) {
        return this;
    }
    int myFixityLevel = sym.getFixityLevel();
    if (myFixityLevel == 0) {
        return this;
    }

    if (sym.getArity() == 1) {
        AlgebraTerm child = this.getArgument(0);
        int childFixityLevel = (child instanceof AlgebraFunctionApplication) ?
        ((SyntacticFunctionSymbol)((AlgebraFunctionApplication) child).getSymbol()).getFixityLevel() : 0;

        if (myFixityLevel >= childFixityLevel) {
            return this;
        }

        // this case sould simply not happen with the default strategy of the parser
        //System.out.println("impossible constalation in FunctionApplication.rearrangeByFixity");
        throw new RuntimeException("impossible constellation in FunctionApplication.rearrangeByFixity");
    } else if (sym.getArity() == 2) {
        AlgebraTerm leftChild = this.getArgument(0);
        AlgebraTerm rightChild = this.getArgument(1);
        int leftChildFixityLevel = 0;
        int rightChildFixityLevel = 0;
        if (this.getArgument(0) instanceof AlgebraFunctionApplication) {
        // String save = leftChild.toString();
        //azazel//System.out.println("Starting to l-rearrange " + save);
        leftChild = ((AlgebraFunctionApplication) leftChild).rearrangeByFixity();
        //azazel//System.out.print("L-Rearranged " + save + " into " + leftChild.toString() + ".\n");
                SyntacticFunctionSymbol leftSym = (SyntacticFunctionSymbol) ((AlgebraFunctionApplication)leftChild).getSymbol();
                if (sym.getFixity() == SyntacticFunctionSymbol.INFIXR && sym.equals(leftSym) && leftChild.getAttribute(new String("FLAG_PARANTHESIS")) == null) {
                    this.replaceArgument(0, leftChild.getArgument(1));
                    ((AlgebraFunctionApplication)leftChild).replaceArgument(1,this);
                    return ((AlgebraFunctionApplication)leftChild).rearrangeByFixity();
                }
        leftChildFixityLevel = leftSym.getFixityLevel();
        if (leftChild.getAttribute(new String("FLAG_PARANTHESIS")) != null) {
            leftChildFixityLevel = 0;
            //azazel//System.out.println("Ignoring " + leftChild.toString() + " because it's inside parathesis\n");
        };
        };
        if (this.getArgument(1) instanceof AlgebraFunctionApplication) {
        // String save = rightChild.toString();
        //azazel//System.out.println("Starting to r-rearrange " + save);
        rightChild = ((AlgebraFunctionApplication) rightChild).rearrangeByFixity();
        //azazel//System.out.print("R-Rearranged " + save + " into " + rightChild.toString() + ".\n");
                SyntacticFunctionSymbol rightSym = (SyntacticFunctionSymbol) ((AlgebraFunctionApplication)rightChild).getSymbol();
                if (sym.getFixity() == SyntacticFunctionSymbol.INFIXL && sym.equals(rightSym) && rightChild.getAttribute(new String("FLAG_PARANTHESIS")) == null) {
                    this.replaceArgument(1, rightChild.getArgument(0));
                    ((AlgebraFunctionApplication)rightChild).replaceArgument(0,this);
                    return ((AlgebraFunctionApplication)rightChild).rearrangeByFixity();
                }
        rightChildFixityLevel = rightSym.getFixityLevel();
        if (rightChild.getAttribute(new String("FLAG_PARANTHESIS")) != null) {
            rightChildFixityLevel = 0;
            //azazel//System.out.println("Ignoring " + rightChild.toString() + " because it's inside parathesis\n");
        };
        };

        if ((myFixityLevel >= leftChildFixityLevel) && (myFixityLevel >= rightChildFixityLevel)) {
        // childs may have changed due to rearrangeByFixity above
        if ((this.getArgument(0) != leftChild) || (this.getArgument(1) != rightChild)) {
            this.replaceArgument(0, leftChild);
            this.replaceArgument(1, rightChild);
            return this.rearrangeByFixity();
        } else {
            return this;
        }
        };

        if (leftChildFixityLevel > rightChildFixityLevel) {
        if (((SyntacticFunctionSymbol)((AlgebraFunctionApplication) leftChild).getSymbol()).getArity() == 1) {
            // (high a) low b -> high (a low b)
            AlgebraTerm a = ((AlgebraFunctionApplication) leftChild).getArgument(0);
            // Term b = rightChild;
            ((AlgebraFunctionApplication) leftChild).replaceArgument(0, this);
            this.replaceArgument(0, a);

            //azazel//System.out.println("(high a) low b -> high (a low b)");
            //azazel//System.out.println("a = " + a.toString());
            //azazel//System.out.println("b = " + b.toString());
            //azazel//System.out.println("r = " + leftChild.toString());

            return ((AlgebraFunctionApplication) leftChild).rearrangeByFixity();
        } else if (((SyntacticFunctionSymbol)((AlgebraFunctionApplication) leftChild).getSymbol()).getArity() == 2) {
            // (a high b) low c -> a high (b low c)
            // Term a = ((FunctionApplication) leftChild).getArgument(0);
            AlgebraTerm b = ((AlgebraFunctionApplication) leftChild).getArgument(1);
            // Term c = rightChild;
            ((AlgebraFunctionApplication) leftChild).replaceArgument(1, this);
            this.replaceArgument(0, b);

            //azazel//System.out.println("(a high b) low c -> a high (b low c)");
            //azazel//System.out.println("a = " + a.toString());
            //azazel//System.out.println("b = " + b.toString());
            //azazel//System.out.println("c = " + c.toString());
            //azazel//System.out.println("r = " + leftChild.toString());

            return ((AlgebraFunctionApplication) leftChild).rearrangeByFixity();
        } else {
            return this;
        }
        } else {
        if (((SyntacticFunctionSymbol)((AlgebraFunctionApplication)  rightChild).getSymbol()).getArity() == 1) {
            // a low (high b) -> high (a low b)
            // this case sould allready be allright
            //azazel//System.out.println("a low (high b) -> high (a low b) case encountered");
            return this;
        } else if (((SyntacticFunctionSymbol)((AlgebraFunctionApplication)  rightChild).getSymbol()).getArity() == 2) {
            // a low (b high c) -> (a low b) high c
            //Term a = leftChild;
            AlgebraTerm b = ((AlgebraFunctionApplication)  rightChild).getArgument(0);
            //Term c = ((FunctionApplication)  rightChild).getArgument(1);
            ((AlgebraFunctionApplication)  rightChild).replaceArgument(0, this);
            this.replaceArgument(1, b);

            //azazel//System.out.println("a low (b high c) -> (a low b) high c");
            //azazel//System.out.println("a = " + a.toString());
            //azazel//System.out.println("b = " + b.toString());
            //azazel//System.out.println("c = " + c.toString());
            //azazel//System.out.println("r = " + rightChild.toString());

            return ((AlgebraFunctionApplication) rightChild).rearrangeByFixity();
        } else {
            return this;
        }
        }
    } else {
        return this;
    }
    }

    @Override
    public int width() {
        return 1;
    }

    @Override
    public aprove.verification.dpframework.BasicStructures.TRSTerm toNewTerm() {
        ArrayList<aprove.verification.dpframework.BasicStructures.TRSTerm> newArgs = new ArrayList<aprove.verification.dpframework.BasicStructures.TRSTerm>();
        for (AlgebraTerm arg : this.getArguments()) {
            newArgs.add(arg.toNewTerm());
        }
        SyntacticFunctionSymbol f = this.getFunctionSymbol();
        aprove.verification.oldframework.BasicStructures.FunctionSymbol newF = f.toNewSymbol();
        return aprove.verification.dpframework.BasicStructures.TRSTerm.createFunctionApplication(newF, ImmutableCreator.create(newArgs));
    }

    @Override
    public IndexSymbol getRootIndexSymbol() {
        return new IndexFunctionSymbol( this.getFunctionSymbol().getName() );
    }
}
