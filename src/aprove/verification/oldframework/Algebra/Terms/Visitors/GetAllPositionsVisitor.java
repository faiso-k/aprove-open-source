package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

public class GetAllPositionsVisitor implements
        CoarseGrainedTermVisitor<Set<Position>> {

    protected Stack<Position> stackOfPositions;

    protected Set<Position> positions;

    public static Set<Position> apply(AlgebraTerm term) {
        return term.apply(new GetAllPositionsVisitor());
    }

    protected GetAllPositionsVisitor() {

        this.stackOfPositions = new Stack<Position>();
        this.stackOfPositions.push(Position.create());

        this.positions = new LinkedHashSet<Position>();
    }

    @Override
    public Set<Position> caseFunctionApp(AlgebraFunctionApplication f) {

        Position currentPosition = this.stackOfPositions.pop();
        this.positions.add(currentPosition);

        for (int i = 0; i < f.getFunctionSymbol().getArity(); i++) {
            this.stackOfPositions.push(currentPosition.shallowcopy().add(i));
            f.getArgument(i).apply(this);
        }

        return this.positions;
    }

    @Override
    public Set<Position> caseVariable(AlgebraVariable v) {

        Position currentPosition = this.stackOfPositions.pop();
        this.positions.add(currentPosition);

        return this.positions;
    }

}


