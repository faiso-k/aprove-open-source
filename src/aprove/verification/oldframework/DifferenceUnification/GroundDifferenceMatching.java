package aprove.verification.oldframework.DifferenceUnification;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class GroundDifferenceMatching {

    public static Set<Set<Position>> apply(Formula phi, Formula psi) throws DifferenceUnificationException {

        Set<Pair<Position,Pair<Equation,Equation>>> equations = GroundDifferenceMatching.getAllEquations(
            Position.create(),phi, psi);

        Set<Pair<Set<PairOfTermsWithPositions>,Set<Position>>> nodes = new LinkedHashSet<Pair<Set<PairOfTermsWithPositions>,
            Set<Position>>>();

        for(Pair<Position,Pair<Equation,Equation>> equation : equations) {

            Position leftPosition  = equation.x.shallowcopy().add(0);
            Position rightPosition = equation.x.shallowcopy().add(1);

            Set<PairOfTermsWithPositions> pairs = new LinkedHashSet<PairOfTermsWithPositions>();
            pairs.add(new PairOfTermsWithPositions(equation.y.x.getLeft(), equation.y.y.getLeft(), leftPosition, leftPosition ));
            pairs.add(new PairOfTermsWithPositions(equation.y.x.getRight(), equation.y.y.getRight(), rightPosition, rightPosition ));

            nodes.add(new Pair<Set<PairOfTermsWithPositions>,Set<Position>>(pairs, new LinkedHashSet<Position>()));

        }

        nodes = GroundDifferenceMatching.leftSearch(nodes);

        while(GroundDifferenceMatching.solutions(nodes).isEmpty() && !nodes.isEmpty()) {
            nodes = GroundDifferenceMatching.leftSearch(GroundDifferenceMatching.rightSearch(nodes));
        }

        if(nodes.isEmpty()) {
            throw new DifferenceUnificationException();
        }else{
            return GroundDifferenceMatching.solutions(nodes);
        }

    }

    private static Set<Pair<Set<PairOfTermsWithPositions>,Set<Position>>> leftSearch(Set<Pair<Set<PairOfTermsWithPositions>,Set<Position>>> nodes) {

        Set<Pair<Set<PairOfTermsWithPositions>,Set<Position>>> result = new LinkedHashSet<Pair<Set<PairOfTermsWithPositions>,Set<Position>>>();

        Stack<Pair<Set<PairOfTermsWithPositions>,Set<Position>>> nodeStack = new Stack<Pair<Set<PairOfTermsWithPositions>,
            Set<Position>>>();
        nodeStack.addAll(nodes);


        while(!nodeStack.isEmpty()) {

            boolean applied = false;

            Pair<Set<PairOfTermsWithPositions>,Set<Position>> node =  nodeStack.pop();

            // delete
            Iterator<PairOfTermsWithPositions> pairIterator = node.x.iterator();
            while(pairIterator.hasNext()) {

                PairOfTermsWithPositions pair = pairIterator.next();

                if(pair.leftTerm.equals(pair.rightTerm)) {
                    pairIterator.remove();
                    applied = true;
                }

            }


            // decompose
            Set<PairOfTermsWithPositions> newPairs = new LinkedHashSet<PairOfTermsWithPositions>();

            pairIterator = node.x.iterator();
            while(pairIterator.hasNext()) {

                PairOfTermsWithPositions pair = pairIterator.next();

                if(!pair.leftTerm.isVariable() && !pair.rightTerm.isVariable()) {
                    if(pair.leftTerm.getSymbol().equals(pair.rightTerm.getSymbol())) {

                        AlgebraFunctionApplication left  = (AlgebraFunctionApplication)pair.leftTerm;
                        AlgebraFunctionApplication    right = (AlgebraFunctionApplication)pair.rightTerm;

                        for(int i=0; i < left.getFunctionSymbol().getArity(); i++) {

                            Position newLeftPostion  = pair.leftPosition.shallowcopy();
                            newLeftPostion.add(i);

                            Position newRightPostion = pair.rightPosition.shallowcopy();
                            newRightPostion.add(i);

                            newPairs.add(new PairOfTermsWithPositions(left.getArgument(i), right.getArgument(i),
                                    newLeftPostion, newRightPostion));

                        }

                        pairIterator.remove();
                        applied = true;

                    }

                }
            }

            node.x.addAll(newPairs);

            if(applied) {
                nodeStack.push(node);
            }else{
                result.add(node);
            }

        }

        return result;
    }

    private static Set<Pair<Set<PairOfTermsWithPositions>,Set<Position>>> rightSearch(Set<Pair<Set<PairOfTermsWithPositions>,Set<Position>>> nodes) {

        Set<Pair<Set<PairOfTermsWithPositions>,Set<Position>>> newNodes =
            new LinkedHashSet<Pair<Set<PairOfTermsWithPositions>, Set<Position>>>();

        for(Pair<Set<PairOfTermsWithPositions>,Set<Position>> node : nodes ) {

            for(PairOfTermsWithPositions pair : node.x) {

                if(!pair.leftTerm.isVariable() && !pair.leftTerm.isConstant()) {

                    AlgebraFunctionApplication functionApplication = (AlgebraFunctionApplication)pair.leftTerm;

                    for(int i=0; i < functionApplication.getArguments().size(); i++) {

                        Pair<Set<PairOfTermsWithPositions>,Set<Position>> newNode =
                            new Pair<Set<PairOfTermsWithPositions>,Set<Position>>(new LinkedHashSet<PairOfTermsWithPositions>(node.x),
                                    new LinkedHashSet<Position>(node.y));

                        Position newLeftPosition = pair.leftPosition.shallowcopy().add(i);
                        newNode.y.add(newLeftPosition);

                        newNode.x.add(new PairOfTermsWithPositions(functionApplication.getArgument(i),
                                pair.rightTerm, newLeftPosition, pair.rightPosition));
                        newNode.x.remove(pair);

                        newNodes.add(newNode);
                    }

                }

            }

        }

        return newNodes;
    }

    private static Set<Set<Position>> solutions(Set<Pair<Set<PairOfTermsWithPositions>,Set<Position>>> nodes) {
        LinkedHashSet<Set<Position>> results = new LinkedHashSet<Set<Position>>();
        for(Pair<Set<PairOfTermsWithPositions>,Set<Position>> possibleResult : nodes) {
            if(possibleResult.x.isEmpty()) {
                results.add(possibleResult.y);
            }
        }
        return results;
    }

    private static Set<Pair<Position,Pair<Equation,Equation>>> getAllEquations(Position position, Formula phi, Formula psi) throws DifferenceUnificationException {

        Set<Pair<Position,Pair<Equation,Equation>>> returnValue = new LinkedHashSet<Pair<Position,Pair<Equation,Equation>>>();

        if(!phi.getClass().equals(psi.getClass())) {
            throw new DifferenceUnificationException();
        }

        if((phi instanceof FormulaTruthValue) && !phi.equals(psi)){
            throw new DifferenceUnificationException();
        }

        if(phi instanceof JunctorFormula) {

            Position newPosition = position.shallowcopy();
            newPosition.add(0);

            returnValue.addAll(GroundDifferenceMatching.getAllEquations(newPosition, ((JunctorFormula)phi).getLeft(), ((JunctorFormula)psi).getLeft()));
            if(((JunctorFormula)phi).getRight() != null) {

                newPosition = position.shallowcopy();
                newPosition.add(1);

                returnValue.addAll(GroundDifferenceMatching.getAllEquations(newPosition, ((JunctorFormula)phi).getRight(),((JunctorFormula)psi).getRight()));
            }

        }

        if(phi instanceof Equation) {
            returnValue.add(new Pair<Position,Pair<Equation,Equation>>(position,new Pair<Equation,Equation>((Equation)phi,(Equation)psi)));
        }

        return returnValue;
    }

}
