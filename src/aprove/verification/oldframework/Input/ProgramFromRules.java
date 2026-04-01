package aprove.verification.oldframework.Input;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** Program creation from a set of rules.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

/* Bug: Duplicate symbols are not checked for compatibility! */

public class ProgramFromRules implements ProgramSource {

    /** Set of rules that is the state of this translator.
     */
    protected Set<Rule> rules;

    @Override
    public Program getProgram() {
    Program prog = Program.create();
    CollectSymbolsVisitor v = new CollectSymbolsVisitor(prog);
    Iterator i = this.rules.iterator();
    while (i.hasNext()) {
        Rule rule = (Rule)i.next();
            prog = v.apply(rule);
    }
    i = this.rules.iterator();
    while (i.hasNext()) {
            Rule rule = (Rule)i.next();
            prog.addRule(rule);
    }
    return prog;
    }

    /** Sets the state of this program source.
     * @param rules Set of rules to build program from.
     */
    public void setRules(Set<Rule> rules) {
    this.rules = rules;
    }

    protected class CollectSymbolsVisitor extends FineGrainedDepthFirstTermVisitor {

    protected Program prog;

    public CollectSymbolsVisitor(Program prog) {
        this.prog = prog;
    }

    @Override
    public void inVariable(AlgebraVariable v) {
        try {
        this.prog.addSort(v.getSymbol().getSort());
        } catch (ProgramException e) {
        // should check if symbols are compatible
        }
    }

    public Program apply(Rule rule) {
        rule.getLeft().apply(this);
        rule.getRight().apply(this);
        return this.prog;
    }

        @Override
        public void inConstructorApp(ConstructorApp cterm) {
            ConstructorSymbol fs = (ConstructorSymbol)cterm.getSymbol();
            try {
                this.prog.addConstructorSymbol(fs);
                this.prog.addSort(fs.getSort());
            } catch (ProgramException e) {
                // should check if symbols are compatible
            }
        }

        @Override
        public void inDefFunctionApp(DefFunctionApp fterm) {
            DefFunctionSymbol fs = (DefFunctionSymbol)fterm.getSymbol();
            try {
                this.prog.addDefFunctionSymbol(fs);
                this.prog.addSort(fs.getSort());
            } catch (ProgramException e) {
                // should check if symbols are compatible
            }
        }
    }

}
