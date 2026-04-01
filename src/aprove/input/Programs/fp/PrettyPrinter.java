package aprove.input.Programs.fp;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** Pretty printer for the FP language.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public class PrettyPrinter implements ProgramPrettyPrinter {

    private StringBuffer pp;
    private int tabsize = 2;

    public PrettyPrinter() {
    super();
    }

    @Override
    public String prettyPrint(Program prog) {
    this.pp = new StringBuffer();
    for (Iterator i = prog.getSorts().iterator(); i.hasNext();) {
        this.printSort((Sort)i.next());
    }
    for (Iterator i = prog.getDefFunctionSymbols().iterator(); i.hasNext();) {
        this.printDefFunctionSymbol(prog, (DefFunctionSymbol)i.next());
    }
    String temp = this.pp.toString();
    this.pp = null;
    return temp;
    }
    private void printSort(Sort s) {
    //    if (s.getName().equals("bool") || s.getName().equals("*")) {return;}
    this.add("structure "); this.add(s); this.nl();
    for (Iterator i = s.getConstructorSymbols().iterator(); i.hasNext();) {
        this.tab();
        this.printConstructorSymbol((ConstructorSymbol)i.next());
    }
    this.nl();
    }
    private void printConstructorSymbol(ConstructorSymbol c) {
    this.add(c); this.add(" : ");
    List<Sort> args = c.getArgSorts();
    if (args.size() != 0) {
        this.printSorts(args);
        this.add(" -> ");
    }
    this.add(c.getSort());
    this.nl();
    }
    private void printSorts(List<Sort> sorts) {
    for (Iterator i = sorts.iterator(); i.hasNext();) {
        this.add((Sort)i.next()); this.add(", ");
    }
    this.chop(); this.chop();
    }
    private void printDefFunctionSymbol(Program prog, DefFunctionSymbol d) {
    //    if (d.getName().equals("if")) {return;}
    this.add("function "); this.add(d); this.add(" : ");
    this.printSorts(d.getArgSorts());
    this.add(" -> ");
    this.add(d.getSort());
    this.nl();
    for (Iterator i = d.getBody(prog).iterator(); i.hasNext();) {
        this.printRule((Rule)i.next());
    }
    this.nl();
    }
    private void printRule(Rule r) {
    this.tab();
    this.printTerm(r.getLeft());
    this.add(" = ");
    this.printTerm(r.getRight());
    this.nl();
    }
    private void printTerm(AlgebraTerm t) {
    this.add(t.getSymbol());
    List<AlgebraTerm> args = t.getArguments();
    if (args != null && args.size() != 0) {
        this.add("(");
        for (Iterator i = args.iterator(); i.hasNext();) {
        this.printTerm((AlgebraTerm)i.next());
        this.add(", ");
        }
        this.chop(); this.chop(); this.add(")");
    }
    }

    private void chop() {
    this.pp.deleteCharAt(this.pp.length()-1);
    }
    private void nl() {
    this.pp.append("\n");
    }
    private void tab() {
    this.add(this.spaces(this.tabsize));
    }
    private String spaces(int n) {
    StringBuffer temp = new StringBuffer();
    for (int i=0; i<n; i++) {
        temp.append(" ");
    }
    return temp.toString();
    }
    private void add(Sort s) {this.add(s.getName());}
    private void add(Symbol s) {this.add(s.getName());}
    private void add(String s) {this.pp.append(s);}

}
