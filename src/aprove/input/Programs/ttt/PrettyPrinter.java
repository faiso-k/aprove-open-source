package aprove.input.Programs.ttt;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** Pretty printer for the TES language.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

class PrettyPrinter implements ProgramPrettyPrinter {

    private StringBuffer pp;
    private int tabsize = 2;

    @Override
    public String prettyPrint(Program prog) {
    Set<VariableSymbol> vars = new HashSet<VariableSymbol>();
    for (Iterator i = prog.getDefFunctionSymbols().iterator(); i.hasNext();) {
        DefFunctionSymbol f = (DefFunctionSymbol)i.next();
        for (Iterator j = f.getBody(prog).iterator(); j.hasNext();) {
        Rule r = (Rule)j.next();
        for (Iterator k = r.getConds().iterator(); k.hasNext();) {
            vars.addAll(((Rule)k.next()).getLeft().getVariableSymbols());
        }
        vars.addAll(r.getLeft().getVariableSymbols());
        }
    }
    this.pp = new StringBuffer();
    this.add("[");
    for (Iterator i = vars.iterator(); i.hasNext();) {
        this.add((VariableSymbol)i.next());
        if (i.hasNext()) {this.add(", ");} else {this.add("]\n");}
    }
    for (Iterator i = prog.getDefFunctionSymbols().iterator(); i.hasNext();) {
        this.printDefFunctionSymbol(prog, (DefFunctionSymbol)i.next());
    }
    String temp = this.pp.toString();
    this.pp = null;
    return temp;
    }
    private void printDefFunctionSymbol(Program prog, DefFunctionSymbol d) {
    for (Iterator i = d.getBody(prog).iterator(); i.hasNext();) {
        this.printRule((Rule)i.next());
        this.nl();
    }
    }
    private void printRule(Rule r) {
    for (Iterator i = r.getConds().iterator(); i.hasNext();) {
        this.printRule((Rule)i.next());
        if (i.hasNext()) {this.add(", ");} else {this.add(" | ");}
    }
    this.printTerm(r.getLeft());
    this.add(" -> ");
    this.printTerm(r.getRight());
    }
    private void printTerm(AlgebraTerm t) {
    this.add(t.getSymbol());
    List args = t.getArguments();
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
