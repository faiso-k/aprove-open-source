package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

public class GetSkeletonVisitor implements CoarseGrainedTermVisitor<AlgebraTerm>{


    protected Set<Position>   waveHoles;
    protected Stack<AlgebraTerm>     stackOfTerms;
    protected Stack<Position> stackOfPosition;

    public static AlgebraTerm apply(AlgebraTerm term, Set<Position> waveHoles) {
        return term.apply(new GetSkeletonVisitor(waveHoles));
    }

    protected GetSkeletonVisitor(Set<Position> waveHoles) {

        this.waveHoles = waveHoles;
        this.stackOfTerms = new Stack<AlgebraTerm>();

        this.stackOfPosition = new Stack<Position>();
        this.stackOfPosition.add(Position.create());

    }

    @Override
    public AlgebraTerm caseFunctionApp(AlgebraFunctionApplication f) {

        Position currentPosition = this.stackOfPosition.pop();

        for(int i=0; i < f.getFunctionSymbol().getArity(); i++) {
            this.stackOfPosition.push(currentPosition.shallowcopy().add(i));
            f.getArgument(i).apply(this);
        }

        LinkedList<AlgebraTerm> arguments = new LinkedList<AlgebraTerm>();
        for(int i=0; i < f.getFunctionSymbol().getArity(); i++) {
            arguments.addFirst(this.stackOfTerms.pop());
        }

        for(int i=0; i < f.getFunctionSymbol().getArity(); i++) {
            if(this.waveHoles.contains(currentPosition.shallowcopy().add(i))) {
                this.stackOfTerms.push(arguments.get(i));
                return this.stackOfTerms.peek();
            }
        }

        this.stackOfTerms.push(AlgebraFunctionApplication.create(f.getFunctionSymbol(), arguments));

        return this.stackOfTerms.peek();
    }

    @Override
    public AlgebraTerm caseVariable(AlgebraVariable v) {
        this.stackOfPosition.pop();
        this.stackOfTerms.push(v.deepcopy());
        return this.stackOfTerms.peek();
    }


}
