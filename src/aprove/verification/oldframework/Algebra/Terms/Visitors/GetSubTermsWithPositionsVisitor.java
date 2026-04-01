/*
 * Created on Oct 24, 2004
 */
package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

/**
 * @author rabe
 */
public class GetSubTermsWithPositionsVisitor implements CoarseGrainedTermVisitor {

    protected Map<AlgebraTerm,List<Position>> mappingOfTermsToPositions;

    protected Stack<Position> stackofPositions;


    public static Map<AlgebraTerm,List<Position>> apply(AlgebraTerm term) {

        GetSubTermsWithPositionsVisitor getSubTermsWithPositionsVisitor = new GetSubTermsWithPositionsVisitor();
        term.apply(getSubTermsWithPositionsVisitor);

        return getSubTermsWithPositionsVisitor.mappingOfTermsToPositions;
    }

    protected GetSubTermsWithPositionsVisitor() {
        this.mappingOfTermsToPositions = new LinkedHashMap<AlgebraTerm, List<Position>>();
        this.stackofPositions = new Stack<Position>();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Algebra.Terms.CoarseGrainedTermVisitor#caseVariable(aprove.verification.oldframework.Algebra.Terms.Variable)
     */
    @Override
    public Object caseVariable(AlgebraVariable v) {

        if( this.stackofPositions.isEmpty() ) {

            LinkedList<Position> linkedList = new LinkedList<Position>();
            linkedList.add(Position.create());

            this.mappingOfTermsToPositions.put(v.deepcopy(),linkedList);
        } else {

            if( this.mappingOfTermsToPositions.containsKey(v)) {
                this.mappingOfTermsToPositions.get(v).add( this.stackofPositions.pop());
            } else {
                LinkedList<Position> linkedList = new LinkedList<Position>();
                linkedList.add(this.stackofPositions.pop());
                this.mappingOfTermsToPositions.put(v.deepcopy(),linkedList);
            }
        }

        return null;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Algebra.Terms.CoarseGrainedTermVisitor#caseFunctionApp(aprove.verification.oldframework.Algebra.Terms.FunctionApplication)
     */
    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {

        if( this.stackofPositions.isEmpty() ) {

            LinkedList<Position> linkedList = new LinkedList<Position>();
            Position position = Position.create();

            linkedList.add(position);
            this.mappingOfTermsToPositions.put(f.deepcopy(),linkedList);

            List<AlgebraTerm> arguments = f.getArguments();

            for(int i=0; i < arguments.size(); i++ ) {

                Position newPosition = position.shallowcopy();
                newPosition.add(i);

                this.stackofPositions.push(newPosition);

                arguments.get(i).apply(this);
            }

        } else {

            Position position = this.stackofPositions.pop();

            if(this.mappingOfTermsToPositions.containsKey(f)) {

                this.mappingOfTermsToPositions.get(f).add(position);

            } else {

                LinkedList<Position> linkedList = new LinkedList<Position>();
                linkedList.add(position);

                this.mappingOfTermsToPositions.put(f.deepcopy(), linkedList );

            }

            List<AlgebraTerm> arguments = f.getArguments();

            for( int i=0; i < arguments.size(); i++){

                Position newPosition = position.shallowcopy();
                newPosition.add(i);

                this.stackofPositions.push(newPosition);

                arguments.get(i).apply(this);
            }

        }

        return null;
    }

}
