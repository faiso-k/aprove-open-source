package aprove.verification.oldframework.Logic.Formulas.Visitors;


import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Syntax.*;

/**
 * Visitor normalises the given the formula by traversing the formula in the depth-left-first order and
 * renaming the variables so that the first variable will be x_0, the second will be x_1 and so on.
 * e.g. f(x,y,z) = g(x,y,x) will be normalised to f(x_0,x_1,x_2) = g(x_0,x_1,x_0);
 */
public class NormalisingVisitor implements FineFormulaVisitor<Formula>, FineGrainedTermVisitor<AlgebraTerm> {

    // next index for next new variable
    protected int                                 variableCounter;

    // Stack for building the renamed copy of the given formula
    protected Stack<TermOrFormula>                stackOfTermOrFormula;

    // Map stores the variables already renamed
    protected Map<VariableSymbol, VariableSymbol> mapOfVariableSymbols;

    /**
     * Applies this visitor to the given formula
     */
    public static Formula apply(Formula formula) {
        return formula.apply(new NormalisingVisitor());
    }

    /**
     * Standard-Constructor for this visitor
     */
    public NormalisingVisitor() {

        // first variable index will be zero
        this.variableCounter = 0;

        // initialise datastructeres for calculation
        this.stackOfTermOrFormula = new Stack<TermOrFormula>();
        this.mapOfVariableSymbols = new LinkedHashMap<VariableSymbol,VariableSymbol>();
    }

    /**
     * Generates a copy of the truthvalue
     */
    @Override
    public Formula caseTruthValue(FormulaTruthValue truthvalFormula) {

        this.stackOfTermOrFormula.push(truthvalFormula.deepcopy());
        return (Formula)this.stackOfTermOrFormula.peek();
    }

    /**
     * Generates a renamed copy of the equation
     */
    @Override
    public Formula caseEquation(Equation eqFormula) {

        eqFormula.getLeft().apply(this);
        eqFormula.getRight().apply(this);

        AlgebraTerm rightTerm = (AlgebraTerm)this.stackOfTermOrFormula.pop();
        AlgebraTerm leftTerm = (AlgebraTerm)this.stackOfTermOrFormula.pop();

        this.stackOfTermOrFormula.push(Equation.create(leftTerm,rightTerm));

        return (Formula)this.stackOfTermOrFormula.peek();
    }

    /**
     * Generates a renamed copy of the and
     */
    @Override
    public Formula caseAnd(And andFormula) {

        andFormula.getLeft().apply(this);
        andFormula.getRight().apply(this);

        Formula rightFormula = (Formula)this.stackOfTermOrFormula.pop();
        Formula leftFormula  = (Formula)this.stackOfTermOrFormula.pop();

        this.stackOfTermOrFormula.push(And.create(leftFormula,rightFormula));

        return (Formula)this.stackOfTermOrFormula.peek();
    }

    /**
     * Generates a renamed copy of the equivalence
     */
    @Override
    public Formula caseEquivalence(Equivalence equivFormula) {

        equivFormula.getLeft().apply(this);
        equivFormula.getRight().apply(this);

        Formula rightFormula = (Formula)this.stackOfTermOrFormula.pop();
        Formula leftFormula  = (Formula)this.stackOfTermOrFormula.pop();

        this.stackOfTermOrFormula.push(Equivalence.create(leftFormula,rightFormula));

        return (Formula)this.stackOfTermOrFormula.peek();
    }

    /**
     * Generates a renamed copy of the implication
     */
    @Override
    public Formula caseImplication(Implication implFormula) {

        implFormula.getLeft().apply(this);
        implFormula.getRight().apply(this);

        Formula rightFormula = (Formula)this.stackOfTermOrFormula.pop();
        Formula leftFormula  = (Formula)this.stackOfTermOrFormula.pop();

        this.stackOfTermOrFormula.push(Implication.create(leftFormula,rightFormula));

        return (Formula)this.stackOfTermOrFormula.peek();
    }

    /**
     * Generates a renamed copy of the not
     */
    @Override
    public Formula caseNot(Not notFormula) {

        notFormula.getLeft().apply(this);

        Formula leftFormula  = (Formula)this.stackOfTermOrFormula.pop();

        this.stackOfTermOrFormula.push(Not.create(leftFormula));

        return (Formula)this.stackOfTermOrFormula.peek();


    }

    /**
     * Generates a renamed copy of the or
     */
    @Override
    public Formula caseOr(Or orFormula) {

        orFormula.getLeft().apply(this);
        orFormula.getRight().apply(this);

        Formula rightFormula = (Formula)this.stackOfTermOrFormula.pop();
        Formula leftFormula  = (Formula)this.stackOfTermOrFormula.pop();

        this.stackOfTermOrFormula.push(Or.create(leftFormula,rightFormula));

        return (Formula)this.stackOfTermOrFormula.peek();
    }

    /**
     * Renames the given variable
     */
    @Override
    public AlgebraTerm caseVariable(AlgebraVariable v) {

        // check if the variable symbol is already know, if so get the variable symbol used previously otherwise
        // create a new one
        if(!this.mapOfVariableSymbols.containsKey(v.getVariableSymbol())) {
            this.mapOfVariableSymbols.put(v.getVariableSymbol(), VariableSymbol.create("x_"+this.variableCounter));
            this.variableCounter++;
        }

        this.stackOfTermOrFormula.push(AlgebraVariable.create(this.mapOfVariableSymbols.get(v.getVariableSymbol())));

        return (AlgebraTerm)this.stackOfTermOrFormula.peek();
    }

    /**
     * Generates a renamed copy of the constructor application
     */
    @Override
    public AlgebraTerm caseConstructorApp(ConstructorApp cterm) {

        for(int i=0; i < cterm.getArguments().size(); i++) {
            cterm.getArgument(i).apply(this);
        }

        LinkedList<AlgebraTerm> arguments = new LinkedList<AlgebraTerm>();

        for(int i=0; i < cterm.getArguments().size(); i++) {
            arguments.addFirst((AlgebraTerm)this.stackOfTermOrFormula.pop());
        }

        this.stackOfTermOrFormula.push( AlgebraFunctionApplication.create(cterm.getFunctionSymbol(), arguments));

        return (AlgebraTerm)this.stackOfTermOrFormula.peek();
    }

    /**
     * Generates a renamed copy of the deffunction application
     */
    @Override
    public AlgebraTerm caseDefFunctionApp(DefFunctionApp fterm) {

        for(int i=0; i < fterm.getArguments().size(); i++) {
            fterm.getArgument(i).apply(this);
        }

        LinkedList<AlgebraTerm> arguments = new LinkedList<AlgebraTerm>();

        for(int i=0; i < fterm.getArguments().size(); i++) {
            arguments.addFirst((AlgebraTerm)this.stackOfTermOrFormula.pop());
        }

        this.stackOfTermOrFormula.push( AlgebraFunctionApplication.create(fterm.getFunctionSymbol(), arguments));

        return (AlgebraTerm)this.stackOfTermOrFormula.peek();
    }

    /**
     * Generates a renamed copy of the metafunction application
     */
    @Override
    public AlgebraTerm caseMetaFunctionApplication(MetaFunctionApplication metaFunctionApplication) {

        for(int i=0; i < metaFunctionApplication.getArguments().size(); i++) {
            metaFunctionApplication.getArgument(i).apply(this);
        }

        LinkedList<AlgebraTerm> arguments = new LinkedList<AlgebraTerm>();

        for(int i=0; i < metaFunctionApplication.getArguments().size(); i++) {
            arguments.addFirst((AlgebraTerm)this.stackOfTermOrFormula.pop());
        }

        this.stackOfTermOrFormula.push( AlgebraFunctionApplication.create(metaFunctionApplication.getFunctionSymbol(), arguments));

        return (AlgebraTerm)this.stackOfTermOrFormula.peek();
    }


}
