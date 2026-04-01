package aprove.verification.oldframework.Rewriting.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

public class FpEvalVisitor implements CoarseGrainedTermVisitor<AlgebraTerm>{

    protected Program program;

    public static AlgebraTerm apply(AlgebraTerm term, Program program) {
        return term.apply(new FpEvalVisitor(program));
    }

    private FpEvalVisitor(Program program) {
        this.program = program;
    }


    @Override
    public AlgebraTerm caseFunctionApp(AlgebraFunctionApplication f) {

        SyntacticFunctionSymbol functionSymbol = f.getFunctionSymbol();

        List<AlgebraTerm> newArguments = new Vector<AlgebraTerm>();

        if( this.program.getPredefFunctionSymbols().contains(functionSymbol) && functionSymbol.getName().startsWith("if_") ) {
            newArguments.add(f.getArgument(0).apply(this));
            newArguments.add(f.getArgument(1).shallowcopy());
            newArguments.add(f.getArgument(2).shallowcopy());
        }else{
            for(int i=0; i < f.getArguments().size(); i++) {
                newArguments.add(f.getArgument(i).apply(this));
            }
        }

        AlgebraTerm newTerm = AlgebraFunctionApplication.create(functionSymbol,newArguments);

        Set<Rule> rulesForFunctionSymbol = this.program.getRuleMapping().get(functionSymbol.getName());

        if(rulesForFunctionSymbol != null) {
            for(Rule rule : rulesForFunctionSymbol) {
                try {
                    AlgebraSubstitution substitution = rule.getLeft().matches(newTerm);
                    return rule.getRight().apply(substitution).apply(this);
                }catch(UnificationException e) {
                }
            }


        }

        return newTerm;
    }

    @Override
    public AlgebraTerm caseVariable(AlgebraVariable v) {
        return v.shallowcopy();
    }


}
