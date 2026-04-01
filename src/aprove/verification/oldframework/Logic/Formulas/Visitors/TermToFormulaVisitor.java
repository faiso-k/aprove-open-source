package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/**
 * This visitor traverses a term and translates it into a formula. By substituting
 * equal-methods by equations. And, or and not will be substituted by the according
 * junctor.
 */
public class TermToFormulaVisitor implements FineGrainedTermVisitor<Formula> {

    protected Stack<TermOrFormula> stack;

    protected Program program;

    public static Formula apply(AlgebraTerm term, Program program) {

        TermToFormulaVisitor termToFormulaVisitor = new TermToFormulaVisitor(term, program);
        return term.apply(termToFormulaVisitor);
    }

    protected TermToFormulaVisitor(AlgebraTerm term, Program program) {

        // init object's variable
        this.stack = new Stack<TermOrFormula>();
        this.program = program;

    }

    @Override
    public Formula caseConstructorApp(ConstructorApp cterm) {

        for(AlgebraTerm term : cterm.getArguments()) {
            term.apply(this);
        }

        SyntacticFunctionSymbol functionSymbol = cterm.getFunctionSymbol();
        int arity = functionSymbol.getArity();

        LinkedList<AlgebraTerm> arguments = new LinkedList<AlgebraTerm>();
        for (int i = 0; i < arity; i++) {
            arguments.addFirst((AlgebraTerm) this.stack.pop());
        }

        this.stack.push(AlgebraFunctionApplication.create(functionSymbol, arguments));

        return null;
    }

    @Override
    public Formula caseDefFunctionApp(DefFunctionApp fterm) {

        for(AlgebraTerm term : fterm.getArguments()) {
            term.apply(this);
        }

        SyntacticFunctionSymbol functionSymbol = fterm.getFunctionSymbol();

        if( "not".equals(functionSymbol.getName() )) {
            this.stack.push(Not.create((Formula)this.stack.pop()));
        }

        if( "and".equals( functionSymbol.getName() )) {

            Formula rightFormula = (Formula) this.stack.pop();
            Formula leftFormula  = (Formula) this.stack.pop();

            this.stack.push( And.create(leftFormula, rightFormula));
            return (Formula) this.stack.peek();
        }

        if( "or".equals( functionSymbol.getName() )) {

            Formula rightFormula = (Formula) this.stack.pop();
            Formula leftFormula  = (Formula) this.stack.pop();

            this.stack.push( Or.create(leftFormula, rightFormula));
            return (Formula) this.stack.peek();
        }

        if( functionSymbol.getName().startsWith("equal")) {

            AlgebraTerm rightTerm = (AlgebraTerm) this.stack.pop();
            AlgebraTerm leftTerm  = (AlgebraTerm) this.stack.pop();

            this.stack.push( Equation.create(leftTerm,rightTerm) );
            return (Formula) this.stack.peek();
        }

        int arity = functionSymbol.getArity();
        LinkedList<AlgebraTerm> arguments = new LinkedList<AlgebraTerm>();

        for( int i = 0; i < arity; i++) {
                arguments.addFirst( (AlgebraTerm)this.stack.pop() );
        }

        this.stack.push(AlgebraFunctionApplication.create( functionSymbol, arguments));

        return null;
    }

    @Override
    public Formula caseMetaFunctionApplication(MetaFunctionApplication metaFunctionApplication) {

        int arity = metaFunctionApplication.getFunctionSymbol().getArity();
        Vector<AlgebraTerm> arguments = new Vector<AlgebraTerm>();

        for (int i = 0; i < arity; i++) {
            arguments.add((AlgebraTerm) this.stack.pop());
        }

        this.stack.push(AlgebraFunctionApplication.create(metaFunctionApplication.getFunctionSymbol(),arguments));

        return null;
    }

    @Override
    public Formula caseVariable(AlgebraVariable v) {
        this.stack.push( v.deepcopy() );
        return null;
    }

}
