package aprove.verification.oldframework.Syntax;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Utility.*;

/** Abstract class for function symbols.
 * Bug: Extend -n==size-n approach for indexing?!
 * @author Peter Schneider-Kamp
 * @version $Id$

 */

public abstract class SyntacticFunctionSymbol extends Symbol implements Checkable {

    private final static Set<String> tttValid;
    static {
        Set<String> tmp = new HashSet<String>();
        tmp.add("+");
        tmp.add("-");
        tmp.add("*");
        tmp.add(":");
        tmp.add(".");
        tmp.add("\\");
        tmp.add("/");
        tmp.add("=");
        tmp.add("|");
        tmp.add("@");
        tmp.add("<");
        tmp.add(">");
        tttValid = Collections.synchronizedSet(tmp);
    }

    protected int arity;
    protected List<Sort> argSorts;
    protected int fixityLevel;
    protected int fixity;

    public static final int NOTINFIX = 0;
    public static final int INFIX = 1;
    public static final int INFIXL = 2;
    public static final int INFIXR = 3;
    public static final int PREFIX = 4;
    public static final int POSTFIX = 5;

    /* constructors */

    protected SyntacticFunctionSymbol(String name, List<Sort> argsorts, Sort sort) {
    super(name, sort);


    this.argSorts = argsorts;
    this.arity = argsorts.size();
    }

    protected SyntacticFunctionSymbol(String name, int arity) {
        super(name,null);
        this.arity = arity;
    }

    public static SyntacticFunctionSymbol create(final String name, final SyntacticFunctionSymbol sym, final List<Sort> args, final Sort sort) {
    if (sym instanceof DefFunctionSymbol) {
        return DefFunctionSymbol.create(name, args, sort);
    } else if (sym instanceof TupleSymbol) {
        return TupleSymbol.create(name, args, sort, ((TupleSymbol)sym).getOrigin());
    } else if (sym instanceof ConstructorSymbol) {
        return ConstructorSymbol.create(name, args, sort);
    }
    throw new RuntimeException("internal error: trying to create function symbol from unknown class!");
    }


    /** Allows CoarseSymbolVisitor objects to visit this object.
     */
    @Override
    final public Object apply(CoarseSymbolVisitor csv) {
    return csv.caseFunctionSymbol(this);
    }

    /* accessors */

    /** Get the arity, i.e. the number of arguments, of this function symbol.
     */
    public int getArity() {
        return this.arity;
    }

    public void setArity(int arity) {
        this.arity = arity;
    }

    /** Returns whether the symbol is a constant or not.
     * @return TRUE, if is a constant, FALSE otherwise
     */
    public boolean isConstant() {
    return (this.arity==0);
    }

    /** Get a list of the sorts the arguments of this function symbol have to have.
     */
    public List<Sort> getArgSorts() {
        return this.argSorts;
    }

    public void setArgSorts(List<Sort> argSorts) {
        this.argSorts = argSorts;
    }

    /** Get the sort the i-th argument of this function symbol has to have.
     */
    public Sort getArgSort(int index) {
    if (index < 0) {
        index += this.argSorts.size();
    }
    return (Sort)this.argSorts.get(index);
    }
    /** Set the sort the i-th argument of this function symbol has to have.
     *  <p>
     *  Note: Use with caution.
     */
    public void setArgSort(int index, Sort sort) {
    if (index < 0) {
        index += this.argSorts.size();
    }
    this.argSorts.set(index, sort);
    }

    public void addArgSort(Sort sort) {
        this.argSorts.add(sort);
        this.arity = this.argSorts.size();
    }

    @Override
    public String toString() {
        return new String(this.name);
    }

    @Override
    public void check(Set checked) {
    if (!checked.contains(this)) {
        super.check(checked);
        if (this.argSorts == null) {
        throw new RuntimeException("argsorts must not be null");
        }
        for (Iterator i=this.argSorts.iterator(); i.hasNext();) {
        ((Sort)i.next()).check(checked);
        }
    }
    }

    @Override
    public String toHTML() {
        StringBuffer res = new StringBuffer();
        if (this instanceof DefFunctionSymbol) {
            res.append("<FONT COLOR=#000088>");
        } else if (this instanceof TupleSymbol) {
            res.append("<FONT COLOR=#006666>");
        } else {
            res.append("<FONT COLOR=#666600>");
        }
        res.append(aprove.verification.oldframework.Algebra.Terms.Visitors.ToHTMLVisitor.escape(this.getName()) + "</FONT>");
        return res.toString();
    }

    public void setFixity(int i) {
    this.fixity = i;
    }

    public void setFixityLevel(int i) {
    this.fixityLevel = i;
    }

    public void setFixity(int type, int level) {
    this.fixity = type;
    this.fixityLevel = level;
    }

    public int getFixity() {
        return this.fixity;
    }

    public int getFixityLevel() {
    return this.fixityLevel;
    }

    public boolean isInfix() {
    return ((this.fixity == SyntacticFunctionSymbol.INFIX) || (this.fixity == SyntacticFunctionSymbol.INFIXL) ||(this.fixity == SyntacticFunctionSymbol.INFIXR));
    }

    /** Determines whether this function symbol has a name that is valid for an infix TTT symbol.
     */
    public boolean isTTTValid() {
    for (int i=0; i<this.name.length(); i++) {
        if (!SyntacticFunctionSymbol.tttValid.contains(Character.valueOf(this.name.charAt(i)).toString())) {
        return false;
        }
    }
    return true;
    }

    public Set<Integer> getModifiablePositions(Program program) {

        Set<Integer> modifiablePositions = new LinkedHashSet<Integer>();

        Set<Rule> rules = program.getRules(this);

        if(((SyntacticFunctionSymbol)this).isRecursive(program)) {

            for(Rule rule : rules) {

                List<AlgebraTerm> leftHandSideArguments = ((AlgebraFunctionApplication)rule.getLeft()).getArguments();
                List<AlgebraTerm> subTerms = rule.getRight().getAllSubterms();

                for(AlgebraTerm term : subTerms) {

                    if(term.getSymbol().equals(this)) {
                        AlgebraFunctionApplication functionApplication = (AlgebraFunctionApplication)term;

                        List<AlgebraTerm> recursiveArguments = functionApplication.getArguments();

                        for(int index = 0; index < this.getArity(); index++) {

                            if(!leftHandSideArguments.get(index).equals(recursiveArguments.get(index))) {
                                modifiablePositions.add(index);
                            }
                        }

                    }

                }
            }

        } else {

            for(Rule rule : rules) {

                AlgebraTerm term = rule.getLeft();

                if( term instanceof AlgebraFunctionApplication) {

                    AlgebraFunctionApplication functionApplication = (AlgebraFunctionApplication)term;

                    int index = 0;

                    for(AlgebraTerm argument : functionApplication.getArguments()) {

                        if( !argument.isVariable() ) {
                            modifiablePositions.add(index);
                        }

                        index++;
                    }
                }
            }
        }

        return modifiablePositions;
    }

    /** Check for recursive definition in the rules of this function symbol.
     */
    public boolean isRecursive(Program prog) {
    Iterator iRule = prog.getRules(this).iterator();
    while (iRule.hasNext()) {
        Rule rule = (Rule)iRule.next();
        Set<Position> pos = rule.getRight().getPositionsWithSymbol(this);
        if (pos.size()!=0) {
        return true;
        }
    }
    return false;
    }

    /** added by azazel as deepcopy is allready implemented in both ConstructorSymbol and DefFunctionSymbol
     */
    @Override
    public abstract Symbol deepcopy();

    public aprove.verification.oldframework.BasicStructures.FunctionSymbol toNewSymbol() {
        return aprove.verification.oldframework.BasicStructures.FunctionSymbol.create(this.getName(), this.getArity());
    }
}
