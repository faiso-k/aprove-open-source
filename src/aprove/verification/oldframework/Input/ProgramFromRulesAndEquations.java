package aprove.verification.oldframework.Input;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** Program creation from a set of rules and a set of equations.
 * @author Stephan Falke
 * @version $Id$
 */

public class ProgramFromRulesAndEquations implements ProgramSource {

    /** Set of rules.
     */
    protected Set<Rule> rules;

    /** Set of equations.
     */
    protected Set<TRSEquation> eqns;

    @Override
    public Program getProgram() {
        Program prog = Program.create();
        CollectSymbolsVisitor v = new CollectSymbolsVisitor(prog);
        Iterator i = this.rules.iterator();
        while (i.hasNext()) {
            Rule rule = (Rule)i.next();
            prog = v.apply(rule);
        }
        i = this.eqns.iterator();
        while (i.hasNext()) {
            TRSEquation eqn = (TRSEquation)i.next();
            prog = v.apply(eqn);
        }
        i = this.rules.iterator();
        while (i.hasNext()) {
            Rule rule = (Rule)i.next();
            prog.addRule(rule);
        }
        i = this.eqns.iterator();
        while (i.hasNext()) {
            TRSEquation eqn = (TRSEquation)i.next();
            prog.addEquation(eqn);
        }
        return prog;
    }

    /** Sets the rules.
     * @param rules Set of rules to build program from.
     */
    public void setRules(Set<Rule> rules) {
        this.rules = rules;
    }

    /** Sets the equations.
     * @param eqns Set of equations to build program from.
     */
    public void setEquations(Set<TRSEquation> eqns) {
        this.eqns = eqns;
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

        public Program apply(TRSEquation eqn) {
            eqn.getOneSide().apply(this);
            eqn.getOtherSide().apply(this);
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
