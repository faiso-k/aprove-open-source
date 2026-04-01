package aprove.verification.oldframework.DifferenceUnification;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class GroundDifferenceUnification {

    private final Set<Position> legalLeftPositions;
    private final Set<Position> legalRightPositions;

    protected GroundDifferenceUnification(final AlgebraTerm s, final AlgebraTerm t) {
        super();

        this.legalLeftPositions = s.getPositions();
        this.legalRightPositions = t.getPositions();
    }

    public static Set<Pair<Set<Position>, Set<Position>>> apply(final AlgebraTerm s, final AlgebraTerm t) {

        final Set<Pair<Set<Position>, Set<Position>>> returnValue =
            new LinkedHashSet<Pair<Set<Position>, Set<Position>>>();

        final GroundDifferenceUnification gdu = new GroundDifferenceUnification(s, t);
        SetOfSearchTreeNodesForGDU nodes = gdu.leftStarSearch(SetOfSearchTreeNodesForGDU.create(s, t));

        while (gdu.solutions(nodes).isEmpty() && !nodes.isEmpty()) {

            nodes = gdu.leftStarSearch(gdu.rightSearch(nodes));

        }

        for (final SearchTreeNodeGDU searchTreeNode : gdu.solutions(nodes)) {
            returnValue.add(new Pair<Set<Position>, Set<Position>>(searchTreeNode.y, searchTreeNode.z));
        }

        return returnValue;
    }

    public SetOfSearchTreeNodesForGDU leftStarSearch(final SetOfSearchTreeNodesForGDU input) {

        final SetOfSearchTreeNodesForGDU returnValue = new SetOfSearchTreeNodesForGDU();
        returnValue.addAll(input);

        final Stack<SearchTreeNodeGDU> stack = new Stack<SearchTreeNodeGDU>();
        stack.addAll(input);

        while (!stack.isEmpty()) {

            SearchTreeNodeGDU current;
            SearchTreeNodeGDU result;

            current = stack.pop();

            result = this.delete(current.deepcopy());
            if (result != null) {
                stack.push(result);
                returnValue.add(result);
                continue;
            }

            result = this.decompose(current.deepcopy());
            if (result != null) {
                stack.push(result);
                returnValue.add(result);
            }

        }

        return returnValue;
    }

    public SetOfSearchTreeNodesForGDU solutions(final SetOfSearchTreeNodesForGDU input) {

        final SetOfSearchTreeNodesForGDU solutions = new SetOfSearchTreeNodesForGDU();

        for (final SearchTreeNodeGDU searchTreeNode : input) {
            if (searchTreeNode.x.isEmpty()) {
                solutions.add(searchTreeNode);
            }
        }

        return solutions;
    }

    public SetOfSearchTreeNodesForGDU rightSearch(final SetOfSearchTreeNodesForGDU input) {

        SetOfSearchTreeNodesForGDU results;
        final SetOfSearchTreeNodesForGDU returnValue = new SetOfSearchTreeNodesForGDU();

        for (final SearchTreeNodeGDU searchTreeNode : input) {

            results = this.hideLeft(searchTreeNode.deepcopy());
            if (results != null) {
                returnValue.addAll(results);
            }

            results = this.hideRight(searchTreeNode.deepcopy());
            if (results != null) {
                returnValue.addAll(results);
            }

        }

        return returnValue;

    }

    public SearchTreeNodeGDU delete(final SearchTreeNodeGDU state) {

        for (final PairOfTermsWithPositions pair : state.x) {
            if (pair.leftTerm.equals(pair.rightTerm)) {
                state.x.remove(pair);
                return state;
            }
        }

        return null;
    }

    public SearchTreeNodeGDU decompose(final SearchTreeNodeGDU state) {

        for (final PairOfTermsWithPositions pair : state.x) {

            final AlgebraTerm leftTerm = pair.leftTerm;
            final AlgebraTerm rightTerm = pair.rightTerm;

            if ((!leftTerm.isVariable() && !leftTerm.isConstant())
                && (!rightTerm.isVariable() && !rightTerm.isConstant())) {

                final AlgebraFunctionApplication functionApplicationLeft = (AlgebraFunctionApplication) leftTerm;
                final AlgebraFunctionApplication functionApplicationRight = (AlgebraFunctionApplication) rightTerm;

                if (functionApplicationLeft.getSymbol().equals(functionApplicationRight.getSymbol())) {

                    for (int arg = 0; arg < functionApplicationLeft.getFunctionSymbol().getArity(); arg++) {

                        final Position newLeftPosition = pair.leftPosition.shallowcopy();
                        newLeftPosition.add(arg);

                        final Position newRightPosition = pair.rightPosition.shallowcopy();
                        newRightPosition.add(arg);

                        state.x.add(PairOfTermsWithPositions.create(functionApplicationLeft.getArgument(arg),
                            functionApplicationRight.getArgument(arg), newLeftPosition, newRightPosition));
                    }

                    state.x.remove(pair);
                    return state;
                }
            }

        }

        return null;
    }

    public SetOfSearchTreeNodesForGDU hideLeft(final SearchTreeNodeGDU state) {

        final SetOfSearchTreeNodesForGDU returnValue = new SetOfSearchTreeNodesForGDU();

        for (final PairOfTermsWithPositions pair : state.x) {

            final AlgebraTerm leftTerm = pair.leftTerm;
            final AlgebraTerm rightTerm = pair.rightTerm;

            if (!leftTerm.isVariable() && !leftTerm.isConstant()) {

                final AlgebraFunctionApplication functionApplication = (AlgebraFunctionApplication) leftTerm;

                for (int arg = 0; arg < functionApplication.getFunctionSymbol().getArity(); arg++) {

                    final SearchTreeNodeGDU stateCopy = state.deepcopy();
                    stateCopy.x.remove(pair);

                    final Position newLeftPosition = pair.leftPosition.shallowcopy();
                    newLeftPosition.add(arg);

                    if (this.legalLeftPositions.contains(newLeftPosition)) {
                        stateCopy.x.add(PairOfTermsWithPositions.create(functionApplication.getArgument(arg),
                            rightTerm, newLeftPosition, pair.rightPosition));

                        stateCopy.y.add(newLeftPosition);

                        returnValue.add(stateCopy);
                    }

                }
                if (returnValue.isEmpty()) {
                    return null;
                } else {
                    return returnValue;
                }
            }

        }

        return null;
    }

    public SetOfSearchTreeNodesForGDU hideRight(final SearchTreeNodeGDU state) {

        final SetOfSearchTreeNodesForGDU returnValue = new SetOfSearchTreeNodesForGDU();

        for (final PairOfTermsWithPositions pair : state.x) {

            final AlgebraTerm leftTerm = pair.leftTerm;
            final AlgebraTerm rightTerm = pair.rightTerm;

            if (!rightTerm.isVariable() && !rightTerm.isConstant()) {

                final AlgebraFunctionApplication functionApplication = (AlgebraFunctionApplication) rightTerm;

                for (int arg = 0; arg < functionApplication.getFunctionSymbol().getArity(); arg++) {

                    final SearchTreeNodeGDU stateCopy = state.deepcopy();
                    stateCopy.x.remove(pair);

                    final Position newRightPosition = pair.rightPosition.shallowcopy();
                    newRightPosition.add(arg);

                    if (this.legalRightPositions.contains(newRightPosition)) {
                        stateCopy.x.add(PairOfTermsWithPositions.create(leftTerm, functionApplication.getArgument(arg),
                            pair.leftPosition, newRightPosition));

                        stateCopy.z.add(newRightPosition);

                        returnValue.add(stateCopy);
                    }

                }
                if (returnValue.isEmpty()) {
                    return null;
                } else {
                    return returnValue;
                }
            }
        }

        return null;
    }

}

class SetOfSearchTreeNodesForGDU extends LinkedHashSet<SearchTreeNodeGDU> {

    public static SetOfSearchTreeNodesForGDU create(final AlgebraTerm s, final AlgebraTerm t) {

        final SetOfSearchTreeNodesForGDU returnValue = new SetOfSearchTreeNodesForGDU();

        final Set<PairOfTermsWithPositions> temp = new LinkedHashSet<PairOfTermsWithPositions>();
        temp.add(PairOfTermsWithPositions.create(s, t, Position.create(), Position.create()));

        final SearchTreeNodeGDU searchTreeNode =
            new SearchTreeNodeGDU(temp, new LinkedHashSet<Position>(), new LinkedHashSet<Position>());
        returnValue.add(searchTreeNode);

        return returnValue;
    }
}

class SearchTreeNodeGDU extends Triple<Set<PairOfTermsWithPositions>, Set<Position>, Set<Position>> {

    public SearchTreeNodeGDU(final Set<PairOfTermsWithPositions> nodes, final Set<Position> leftAnnotations,
            final Set<Position> rightAnnotations) {
        super(nodes, leftAnnotations, rightAnnotations);
    }

    public SearchTreeNodeGDU deepcopy() {

        final Set<PairOfTermsWithPositions> copyNode = new LinkedHashSet<PairOfTermsWithPositions>();
        for (final PairOfTermsWithPositions pair : this.x) {
            copyNode.add(pair.deepcopy());
        }

        final Set<Position> copyLeftAnnotations = new LinkedHashSet<Position>();
        for (final Position position : this.y) {
            copyLeftAnnotations.add(position.shallowcopy());
        }

        final Set<Position> copyRightAnnotations = new LinkedHashSet<Position>();
        for (final Position position : this.z) {
            copyRightAnnotations.add(position.shallowcopy());
        }
        return new SearchTreeNodeGDU(copyNode, copyLeftAnnotations, copyRightAnnotations);

    }

    @Override
    public int hashCode() {

        int hashCode = 0;

        for (final PairOfTermsWithPositions pair : this.x) {
            hashCode += pair.hashCode();
        }

        return hashCode;
    }

    @Override
    public boolean equals(final Object object) {

        if (!(object instanceof SearchTreeNodeGDU)) {
            return false;
        }

        final SearchTreeNodeGDU that = (SearchTreeNodeGDU) object;

        return (this.y.containsAll(that.y) && that.y.containsAll(this.y))
            && (this.z.containsAll(that.z) && that.z.containsAll(this.z))
            && (this.x.containsAll(that.x) && that.x.containsAll(this.x));

    }
}
