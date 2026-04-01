package aprove.verification.oldframework.Syntax;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Utility.*;


/** A sort symbol is an unsorted symbol that has a number of constructors.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public class Sort extends UnsortedSymbol implements Checkable {

    //public static final Sort standard = Sort.create("?|?");
    public static final String standardName = "*|?";
    protected Hashtable<String,ConstructorSymbol> sig;
    protected List<ConstructorSymbol> constructorSymbols;
    protected int empty;
    protected AlgebraTerm witnessTerm = null;
    protected DefFunctionSymbol equalOp = null;

    /* constructors */
    public Sort() {
    }

    public void setConstructorSymbols(List<ConstructorSymbol> constructorSymbol) {
        this.constructorSymbols = constructorSymbol;
    }



    private Sort(String name, Hashtable<String,ConstructorSymbol> sig, List<ConstructorSymbol> cons) {
        super(name);
        this.sig = sig;
        this.constructorSymbols = cons;
        this.empty = -1; // unknown if empty
    }

    private Sort(String name, Hashtable<String,ConstructorSymbol> sig, List<ConstructorSymbol> cons, AlgebraTerm witnessterm, DefFunctionSymbol equalOp) {
        this(name,sig,cons);
        this.equalOp = equalOp;
        this.witnessTerm = witnessterm;
    }

    public static Sort create(String name, List<ConstructorSymbol> cons) {
        Hashtable<String,ConstructorSymbol> sig = new Hashtable<String,ConstructorSymbol>();
        for(ConstructorSymbol constructorSymbol : cons) {
            sig.put(constructorSymbol.getName(), constructorSymbol);
        }
        return new Sort(name, sig, cons);
    }

    public static Sort create(String name, List<ConstructorSymbol> cons, AlgebraTerm witnessterm, DefFunctionSymbol equalOp) {
        Hashtable<String,ConstructorSymbol> sig = new Hashtable<String,ConstructorSymbol>();
        for(ConstructorSymbol constructorSymbol : cons) {
            sig.put(constructorSymbol.getName(), constructorSymbol);
        }
        return new Sort(name, sig, cons, witnessterm, equalOp);
    }


    public static Sort create(String name) {
    return new Sort(name, new Hashtable<String,ConstructorSymbol>(), new Vector<ConstructorSymbol>());
    }

    /* build a vector of standard sorts
     * @param size
     * @return a vector of standard sorts
     */
    public static Vector<Sort> getVectorOfStandardSort(int size,Sort poly){
        Vector<Sort> vos = new Vector<Sort>();
    for (int i=0;i<size;i++){
           vos.add(poly);
    }
    return vos;
    }

    /* accessor methods */

    /** Add a constructor symbol to this sort.
     */
    public void addConstructorSymbol(ConstructorSymbol con) {
    if (this.sig.get(con.getName()) == null) {
        this.constructorSymbols.add(con);
        this.sig.put(con.getName(), con);
        } else {
            if (!this.sig.get(con.getName()).equals(con)) {
                throw new RuntimeException("sort already has constructor '"+con.getName()+"'");
            }
    }
    }

    /** Get the i-th constructor symbol of this sort.
     */
    public ConstructorSymbol getConstructorSymbol(int index) {
    return (ConstructorSymbol)this.constructorSymbols.get(index);
    }

    public List<ConstructorSymbol> getConstructorSymbols() {
    return this.constructorSymbols;
    }

    /** Set the empty status of this sort.
     *  <p>
     *  Note: This should only be used to reset the value to -1 or if
     *  the emptiness (or not-emptiness) is known by construction.
     */
    public void setEmpty(int empty) {
    this.empty=empty;
    }

    /** Get the empty status of this sort.
     *  <p>
     *  Note: -1 means the status is unknown.
     */
    public int getEmpty() {
    return this.empty;
    }

    @Override
    public String toString() {
    StringBuffer temp = new StringBuffer(this.name+": [");
    for (Iterator i = this.constructorSymbols.iterator(); i.hasNext();) {
        temp.append(((ConstructorSymbol)i.next()).getName());
        if (i.hasNext()) {
            temp.append(", ");
        }
    }
    return temp.toString()+"]";
    }

    @Override
    public String verboseToString() {
    return "{sort "+this.toString()+"}";
    }

    /* misc methods */

    /** Check sort for emptiness.
     */
    public boolean isEmpty() {
    if (this.empty == -1) {
        HashSet open = new HashSet();
        HashSet closed = new HashSet();
        open.add(this);
        while (!open.isEmpty()) {
        Sort s = (Sort)open.iterator().next();
        open.remove(s);
        if (!closed.contains(s)) {
            closed.add(s);
            boolean reflexive = true;
            for (int i=0; i<s.getConstructorSymbols().size(); i++) {
            ConstructorSymbol c = s.getConstructorSymbol(i);
            boolean sreflexive = c.isReflexive();
            if (!sreflexive) {
                for (int j=0; j<c.getArgSorts().size(); j++) {
                if (c.getArgSort(j) != s) {
                    open.add(c.getArgSort(j));
                }
                }
                if (c.getArgSorts().size() == 0) {
                s.setEmpty(0);
                }
            }
            reflexive = reflexive && sreflexive;
            }
            if (reflexive) {
            s.setEmpty(1);
            }
        }
        }
        boolean change = true;
        while (change) {
        change = false;
        for (Iterator i=closed.iterator(); i.hasNext();) {
            Sort s = (Sort)i.next();
            if (s.getEmpty() == -1) {
            boolean allempty = true;
            for (int j=0; j<s.getConstructorSymbols().size(); j++) {
                ConstructorSymbol c = s.getConstructorSymbol(j);
                if (!c.isReflexive()) {
                boolean nonempty = true;
                boolean empty = false;
                for (int k=0; k<c.getArgSorts().size(); k++) {
                    if (c.getArgSort(k) != s) {
                    nonempty = nonempty && (c.getArgSort(k).getEmpty()==0);
                    empty = empty || (c.getArgSort(k).getEmpty()==1);
                    }
                }
                if (nonempty) {
                    s.setEmpty(0);
                    change = true;
                }
                allempty = allempty && empty;
                }
            }
            if (allempty) {
                s.setEmpty(1);
                change = true;
            }
            }
        }
        }
        if (this.empty == -1) {
        this.empty = 1;
        }
    }
    return this.empty == 1;
    }

    @Override
    public void check(Set checked) {
    if (!checked.contains(this)) {
        super.check(checked);
        if ((this.empty != 0) && (this.empty != -1) && (this.empty != 1)) {
        throw new RuntimeException("empty must be -1, 0 or 1, but not "+Integer.valueOf(this.empty).toString());
        }
        if (this.constructorSymbols == null) {
        throw new RuntimeException("cons must not be null");
        }
        for (Iterator i=this.constructorSymbols.iterator(); i.hasNext();) {
        ((ConstructorSymbol)i.next()).check(checked);
        }
    }
    }

    public AlgebraTerm getWitnessTerm() {
    return this.witnessTerm;
    }

    public void setWitnessTerm(AlgebraTerm wt) {
    this.witnessTerm = wt;
    }

    public DefFunctionSymbol getEqualOp() {
    return this.equalOp;
    }

    public void setEqualOp(DefFunctionSymbol eq) {
    this.equalOp = eq;
    }

    @Override
    public boolean equals(Object object) {
        if(object instanceof Sort) {
            Sort that = ((Sort)object);
            return this.constructorSymbols.equals(that.getConstructorSymbols()) &&
                (this.witnessTerm != null && that.witnessTerm != null ? this.witnessTerm.equals(that.witnessTerm) : true);
        }
        return false;
    }

    private final static String INDENT_STRING = "  ";

    private int indent(String head, StringBuffer sb, int indent) {
        indent = Sort.preindent(head, sb, indent);
        Sort.level(sb, indent);
        return indent;
    }

    private static int preindent(String head, StringBuffer sb, int indent) {
        sb.append("(");
        sb.append(head);
        indent++;
        return indent;
    }

    private static int dedent(StringBuffer sb, int indent) {
        indent--;
        Sort.level(sb, indent);
        sb.append(")");
        return indent;
    }

    private static void level(StringBuffer sb, int indent) {
        sb.append("\n");
        for (int i = 0; i < indent; i++) {
            sb.append(Sort.INDENT_STRING);
        }
    }

    public void toACL2(StringBuffer sb, int indent, FreshNameGenerator fng, boolean fullLists) {
        indent = this.indent("defun "+fng.getFreshName("is"+this.getName(), true)+" (x)", sb, indent);
        indent = Sort.preindent("or", sb, indent);
        for (ConstructorSymbol cons : this.getConstructorSymbols()) {
            int arity = cons.getArity();
            Sort.level(sb, indent);
            indent = Sort.preindent("and", sb, indent);
            for (int i = 0; i < (fullLists ? arity+1 : arity); i++) {
                Sort.level(sb,indent);
                indent = this.indent("consp", sb, indent);
                for (int j = 0; j < i; j++) {
                    indent = this.indent("cdr", sb, indent);
                }
                sb.append("x");
                for (int j = 0; j < i; j++) {
                    indent = Sort.dedent(sb, indent);
                }
                indent = Sort.dedent(sb, indent);
            }
            Sort.level(sb, indent);
            indent = this.indent("eq", sb, indent);
            sb.append("'");
            sb.append(fng.getFreshName(cons.getName(), true));
            Sort.level(sb, indent);
            if (fullLists || arity > 0) {
                indent = this.indent("car", sb, indent);
            }
            sb.append("x");
            if (fullLists || arity > 0) {
                indent = Sort.dedent(sb, indent);
            }
            indent = Sort.dedent(sb, indent);
            for (int i = 0; i < arity; i++) {
                Sort.level(sb, indent);
                indent = this.indent(fng.getFreshName("is"+cons.getArgSort(i).getName(), true), sb, indent);
                if (fullLists || i+1 < arity) {
                    indent = this.indent("car", sb, indent);
                }
                for (int j = 0; j <= i; j++) {
                    indent = this.indent("cdr", sb, indent);
                }
                sb.append("x");
                for (int j = 0; j <= i; j++) {
                    indent = Sort.dedent(sb, indent);
                }
                if (fullLists || i+1 < arity) {
                    indent = Sort.dedent(sb, indent);
                }
                indent = Sort.dedent(sb, indent);
            }
            if (fullLists) {
                // check if last element of list is a ACL-nil
                Sort.level(sb, indent);
                indent = this.indent("eq", sb, indent);
                for (int i = 0; i < arity+1; i++) {
                    indent = this.indent("cdr", sb, indent);
                }
                sb.append("x");
                for (int i = 0; i < arity+1; i++) {
                    indent = Sort.dedent(sb, indent);
                }
                Sort.level(sb, indent);
                sb.append("'nil");
                // dedent for eq
                indent = Sort.dedent(sb, indent);
            }
            // dedent for and
            indent = Sort.dedent(sb, indent);
        }
        // dedent for or
        indent = Sort.dedent(sb, indent);
        // dedent for defun
        indent = Sort.dedent(sb, indent);
    }

    public AlgebraTerm getWitnessTermCandidate() {
        AlgebraTerm witness = this.getWitnessTerm();
        if (witness == null) {
            for (ConstructorSymbol cons : this.getConstructorSymbols()) {
                if (cons.getArity() == 0) {
                    witness = AlgebraFunctionApplication.create(cons);
                    break;
                }
            }
        }
        return witness;
    }

}
