package aprove.verification.oldframework.DifferenceUnification;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Algebra.Terms.Visitors.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class DifferenceUnification {

    Set<Position> positionsInLeftTerm;
    Set<Position> positionsInRightTerm;

    public DifferenceUnification(AlgebraTerm leftTerm, AlgebraTerm rightTerm) {
        this.positionsInLeftTerm = GetAllPositionsVisitor.apply(leftTerm);
        this.positionsInRightTerm = GetAllPositionsVisitor.apply(rightTerm);
    }

    public static Set<Triple<Set<Position>,Set<Position>, AlgebraSubstitution>> apply(AlgebraTerm s, AlgebraTerm t) {

        Set<Triple<Set<Position>,Set<Position>,AlgebraSubstitution>> returnValue = new
            LinkedHashSet<Triple<Set<Position>,Set<Position>, AlgebraSubstitution>>();

        DifferenceUnification du = new DifferenceUnification(s,t);
        SetOfSearchTreeNodesForDU nodes  = du.search(SetOfSearchTreeNodesForDU.create(s,t));

        for(SearchTreeNodeDU searchTreeNode:du.solutions(nodes)) {
            returnValue.add(new Triple<Set<Position>,Set<Position>, AlgebraSubstitution>(searchTreeNode.x,searchTreeNode.y, searchTreeNode.z));
        }

        return returnValue;
    }

    public SetOfSearchTreeNodesForDU search(SetOfSearchTreeNodesForDU input) {

        SetOfSearchTreeNodesForDU returnValue = new SetOfSearchTreeNodesForDU();
        returnValue.addAll(input);

        Stack<SearchTreeNodeDU> stack = new Stack<SearchTreeNodeDU>();
        stack.addAll(input);

        while(!stack.isEmpty()) {

            SearchTreeNodeDU current = stack.pop();

            SearchTreeNodeDU result = this.delete(current);
            if(result != null) {
                stack.push(result);
                returnValue.add(result);

            }

            result = this.decompose(current);
            if(result != null) {
                stack.push(result);
                returnValue.add(result);
            }

//            result = this.imitateLeft(current);
//            if(result != null) {
//                if(!stack.contains(result))
//                    stack.push(result);
//                returnValue.add(result);
//            }
//
//            result = this.imitateRight(current);
//            if(result != null) {
//                if(!stack.contains(result))
//                    stack.push(result);
//                returnValue.add(result);
//            }

            result = this.eliminateLeft(current);
            if(result != null) {
                if(!stack.contains(result)) {
                    stack.push(result);
                }
                returnValue.add(result);
            }

            result = this.eliminateRight(current);
            if(result != null) {
                stack.push(result);
                returnValue.add(result);
            }

            SetOfSearchTreeNodesForDU results = this.hideLeft(current);
            if(results != null) {
                stack.addAll(results);
                returnValue.addAll(results);

            }

            results = this.hideRight(current);
            if(results != null) {
                stack.addAll(results);
                returnValue.addAll(results);

            }
        }

        return returnValue;

    }

    public SetOfSearchTreeNodesForDU solutions(SetOfSearchTreeNodesForDU input ) {

        SetOfSearchTreeNodesForDU solutions = new SetOfSearchTreeNodesForDU();

        for(SearchTreeNodeDU searchTreeNode : input) {
            if(searchTreeNode.w.isEmpty()) {
                    solutions.add(searchTreeNode);
            }
        }

        return solutions;
    }

    public SearchTreeNodeDU delete(SearchTreeNodeDU current) {

        SearchTreeNodeDU state = current.deepcopy();

        for(PairOfTermsWithPositions pair: current.w){
            if (pair.leftTerm.equals(pair.rightTerm)) {
                state.w.remove(pair);
                return state;
            }
        }

        return null;
    }


    public SearchTreeNodeDU decompose(SearchTreeNodeDU current) {

        SearchTreeNodeDU state = current.deepcopy();

        for(PairOfTermsWithPositions pair : current.w) {

            AlgebraTerm leftTerm  = pair.leftTerm;
            AlgebraTerm rightTerm = pair.rightTerm;

            if( (!leftTerm.isVariable() &&  !leftTerm.isConstant()) &&
                (!rightTerm.isVariable() && !rightTerm.isConstant())){

                AlgebraFunctionApplication functionApplicationLeft  = (AlgebraFunctionApplication)leftTerm;
                AlgebraFunctionApplication functionApplicationRight = (AlgebraFunctionApplication)rightTerm;

                if( functionApplicationLeft.getSymbol().equals(functionApplicationRight.getSymbol())) {

                    for(int arg = 0; arg < functionApplicationLeft.getFunctionSymbol().getArity(); arg++) {

                        Position newLeftPosition = pair.leftPosition.shallowcopy();
                        newLeftPosition.add(arg);

                        Position newRightPosition = pair.rightPosition.shallowcopy();
                        newRightPosition.add(arg);

                        state.w.add( PairOfTermsWithPositions.create(functionApplicationLeft.getArgument(arg),
                                functionApplicationRight.getArgument(arg), newLeftPosition, newRightPosition));
                    }

                    state.w.remove(pair);
                    return state;
                }
            }

        }

        return null;
    }

    public SearchTreeNodeDU imitateLeft(SearchTreeNodeDU current) {

    outer:for(PairOfTermsWithPositions pair : current.w) {

            SearchTreeNodeDU state = current.deepcopy();

            AlgebraTerm leftTerm  = pair.leftTerm;
            AlgebraTerm rightTerm = pair.rightTerm;

            if(leftTerm.isVariable() && !rightTerm.isConstant() && !rightTerm.isVariable()) {

                AlgebraVariable variable = (AlgebraVariable)leftTerm;

                FreshVarGenerator freshVarGenerator = new FreshVarGenerator(pair.getAllUsedVariables());

                AlgebraFunctionApplication functionApplication = (AlgebraFunctionApplication)rightTerm;
                List<AlgebraTerm> args = new Vector<AlgebraTerm>();
                for(int i=0; i < functionApplication.getFunctionSymbol().getArity(); i++) {

                    AlgebraVariable newVariable = freshVarGenerator.getFreshVariable(variable,false);

                    Position newRightPosition = pair.rightPosition.shallowcopy().add(i);

                    if(!this.positionsInRightTerm.contains(newRightPosition)) {
                        continue outer;
                    }

                    state.w.add( new PairOfTermsWithPositions(newVariable,functionApplication.getArgument(i),
                            pair.leftPosition.shallowcopy().add(i), newRightPosition));

                    args.add(newVariable);
                }

                AlgebraFunctionApplication newfunctionApplication;
                if(functionApplication instanceof DefFunctionApp) {
                    newfunctionApplication = AlgebraFunctionApplication.create(functionApplication.
                            getFunctionSymbol(),args);
                }else{
                    newfunctionApplication = AlgebraFunctionApplication.create(functionApplication.
                            getFunctionSymbol(),args);
                }

                AlgebraSubstitution newSubstitution = AlgebraSubstitution.create();
                newSubstitution.put(variable.getVariableSymbol(),newfunctionApplication);

                state.z = state.z.compose(newSubstitution);

                state.w.remove(pair);

                for(PairOfTermsWithPositions rewrittePair : state.w) {
                    rewrittePair.leftTerm  = rewrittePair.leftTerm.apply(newSubstitution);
                    rewrittePair.rightTerm = rewrittePair.rightTerm.apply(newSubstitution);
                }
                return state;

            }

        }

        return null;
    }

    public SearchTreeNodeDU imitateRight(SearchTreeNodeDU current) {

    outer:for(PairOfTermsWithPositions pair : current.w) {

            SearchTreeNodeDU state = current.deepcopy();

            AlgebraTerm leftTerm  = pair.leftTerm;
            AlgebraTerm rightTerm = pair.rightTerm;

            if(rightTerm.isVariable() && !leftTerm.isConstant() && !leftTerm.isVariable()) {

                AlgebraVariable variable = (AlgebraVariable)rightTerm;

                FreshVarGenerator freshVarGenerator = new FreshVarGenerator(pair.getAllUsedVariables());

                AlgebraFunctionApplication functionApplication = (AlgebraFunctionApplication)leftTerm;
                List<AlgebraTerm> args = new Vector<AlgebraTerm>();
                for(int i=0; i < functionApplication.getFunctionSymbol().getArity(); i++) {

                    AlgebraVariable newVariable = freshVarGenerator.getFreshVariable(variable,false);

                    Position newLeftPosition = pair.leftPosition.shallowcopy().add(i);

                    if(!this.positionsInLeftTerm.contains(newLeftPosition)) {
                        continue outer;
                    }

                    state.w.add( new PairOfTermsWithPositions(newVariable,functionApplication.getArgument(i).deepcopy(),
                            newLeftPosition, pair.rightPosition.shallowcopy().add(i)));

                    args.add(newVariable);
                }

                AlgebraFunctionApplication newFunctionApplication;
                if(functionApplication instanceof DefFunctionApp) {
                    newFunctionApplication = AlgebraFunctionApplication.create(functionApplication.
                            getFunctionSymbol(),args);
                }else{
                    newFunctionApplication = AlgebraFunctionApplication.create(functionApplication.
                            getFunctionSymbol(),args);
                }

                AlgebraSubstitution newSubstitution = AlgebraSubstitution.create();
                newSubstitution.put(variable.getVariableSymbol(), newFunctionApplication);

                state.z = state.z.compose(newSubstitution);

                state.w.remove(pair);

                for(PairOfTermsWithPositions rewrittePair : state.w) {
                    rewrittePair.leftTerm  = rewrittePair.leftTerm.apply(newSubstitution);
                    rewrittePair.rightTerm = rewrittePair.rightTerm.apply(newSubstitution);
                }

                return state;

            }
        }

        return null;

    }

    public SearchTreeNodeDU eliminateLeft(SearchTreeNodeDU current) {

        SearchTreeNodeDU state = current.deepcopy();

        for(PairOfTermsWithPositions pair : state.w) {

            AlgebraTerm leftTerm  = pair.leftTerm;
            AlgebraTerm rightTerm = pair.rightTerm;

            if(leftTerm.isVariable() && rightTerm.isVariable()) {

                AlgebraVariable variable = (AlgebraVariable)leftTerm;

                if(rightTerm.getVariableSymbols().contains(variable.getSymbol())) {
                    continue;
                }else{

                    AlgebraSubstitution newSubstitution = AlgebraSubstitution.create();
                    newSubstitution.put(variable.getVariableSymbol(), rightTerm);

                    for(PairOfTermsWithPositions substitutionPair : state.w) {
                        substitutionPair.leftTerm  = substitutionPair.leftTerm.apply(newSubstitution);
                        substitutionPair.rightTerm = substitutionPair.rightTerm.apply(newSubstitution);
                    }

                    state.z = state.z.compose(newSubstitution);
                    state.w.remove(pair);

                    return state;
                }

            }

        }

        return null;

    }

    public SearchTreeNodeDU eliminateRight(SearchTreeNodeDU current) {

        SearchTreeNodeDU state = current.deepcopy();

        for(PairOfTermsWithPositions pair : state.w) {

            AlgebraTerm leftTerm  = pair.leftTerm;
            AlgebraTerm rightTerm = pair.rightTerm;

            if(rightTerm.isVariable() && leftTerm.isVariable()) {

                AlgebraVariable variable = (AlgebraVariable)rightTerm;

                if(leftTerm.getVariableSymbols().contains(variable.getSymbol())) {
                    continue;
                }else{

                    AlgebraSubstitution newSubstitution = AlgebraSubstitution.create();
                    newSubstitution.put(variable.getVariableSymbol(), leftTerm);

                    for(PairOfTermsWithPositions substitutionPair : state.w) {
                        substitutionPair.leftTerm  = substitutionPair.leftTerm.apply(newSubstitution);
                        substitutionPair.rightTerm = substitutionPair.rightTerm.apply(newSubstitution);
                    }

                    state.z = state.z.compose(newSubstitution);
                    state.w.remove(pair);

                    return state;
                }

            }

        }

        return null;
    }

    public SetOfSearchTreeNodesForDU hideLeft(SearchTreeNodeDU state) {

        outer: for(PairOfTermsWithPositions pair : state.w) {

            SetOfSearchTreeNodesForDU returnValue = new SetOfSearchTreeNodesForDU();

            AlgebraTerm leftTerm  = pair.leftTerm;
            AlgebraTerm rightTerm = pair.rightTerm;

            if(!leftTerm.isVariable() && !leftTerm.isConstant() ) {

                AlgebraFunctionApplication functionApplication = (AlgebraFunctionApplication)leftTerm;

                for(int arg=0; arg < functionApplication.getFunctionSymbol().getArity(); arg++) {

                    SearchTreeNodeDU stateCopy = state.deepcopy();
                    stateCopy.w.remove(pair);

                    Position newLeftPosition = pair.leftPosition.shallowcopy();
                    newLeftPosition.add(arg);

                    if(!this.positionsInLeftTerm.contains(newLeftPosition)) {
                        continue outer;
                    }

                    stateCopy.w.add(PairOfTermsWithPositions.create(functionApplication.getArgument(arg), rightTerm,
                            newLeftPosition, pair.rightPosition));

                    stateCopy.x.add(newLeftPosition);

                    returnValue.add(stateCopy);
                }

                return returnValue;
            }

        }

        return null;
    }

    public SetOfSearchTreeNodesForDU hideRight(SearchTreeNodeDU state) {

        outer: for(PairOfTermsWithPositions pair : state.w) {

            SetOfSearchTreeNodesForDU returnValue = new SetOfSearchTreeNodesForDU();

            AlgebraTerm leftTerm  = pair.leftTerm;
            AlgebraTerm rightTerm = pair.rightTerm;

            if(!rightTerm.isVariable() && !rightTerm.isConstant() ) {

                AlgebraFunctionApplication functionApplication = (AlgebraFunctionApplication)rightTerm;

                for(int arg=0; arg < functionApplication.getFunctionSymbol().getArity(); arg++) {

                    SearchTreeNodeDU stateCopy = state.deepcopy();
                    stateCopy.w.remove(pair);

                    Position newRightPosition = pair.rightPosition.shallowcopy();
                    newRightPosition.add(arg);

                    if(!this.positionsInRightTerm.contains(newRightPosition)) {
                        continue outer;
                    }

                    stateCopy.w.add(PairOfTermsWithPositions.create(leftTerm,functionApplication.getArgument(arg),
                            pair.leftPosition, newRightPosition));

                    stateCopy.y.add(newRightPosition);

                    returnValue.add(stateCopy);
                }

                return returnValue;
            }
        }


        return null;
    }

}

class SetOfSearchTreeNodesForDU extends LinkedHashSet<SearchTreeNodeDU> {

    public static SetOfSearchTreeNodesForDU create(AlgebraTerm s, AlgebraTerm t) {

        SetOfSearchTreeNodesForDU returnValue = new SetOfSearchTreeNodesForDU();

        Set<PairOfTermsWithPositions> temp = new LinkedHashSet<PairOfTermsWithPositions>();
        temp.add(PairOfTermsWithPositions.create(s,t,Position.create(),Position.create()));

         SearchTreeNodeDU searchTreeNode = new SearchTreeNodeDU(temp, new LinkedHashSet<Position>(),
            new LinkedHashSet<Position>(), AlgebraSubstitution.create());
        returnValue.add(searchTreeNode);

        return returnValue;
    }
}

class SearchTreeNodeDU extends Quadruple<Set<PairOfTermsWithPositions>,Set<Position>,Set<Position>,AlgebraSubstitution> {

    public SearchTreeNodeDU(Set<PairOfTermsWithPositions> nodes, Set<Position> leftAnnotations, Set<Position> rightAnnotations, AlgebraSubstitution substitution) {
        super(nodes, leftAnnotations, rightAnnotations, substitution);
    }

    public SearchTreeNodeDU deepcopy() {

        Set<PairOfTermsWithPositions> copyNode = new LinkedHashSet<PairOfTermsWithPositions>();
        for(PairOfTermsWithPositions pair : this.w){
            copyNode.add(pair.deepcopy());
        }

        Set<Position> copyLeftAnnotations = new LinkedHashSet<Position>();
        for(Position position : this.x) {
            copyLeftAnnotations.add(position.shallowcopy());
        }

        Set<Position> copyRightAnnotations = new LinkedHashSet<Position>();
        for(Position position : this.y) {
            copyRightAnnotations.add(position.shallowcopy());
        }

        return new SearchTreeNodeDU(copyNode, copyLeftAnnotations, copyRightAnnotations, this.z.deepcopy());

    }

    @Override
    public int hashCode() {

        int hashCode = 0;

        for(PairOfTermsWithPositions pair : this.w) {
            hashCode += pair.hashCode();
        }

        return hashCode;
    }

    @Override
    public boolean equals(Object object) {

        if(!(object instanceof SearchTreeNodeDU)){
            return false;
        }

        SearchTreeNodeDU that = (SearchTreeNodeDU)object;
        return super.equals(that);

    }
}
