package aprove.verification.oldframework.Algebra.Terms.Visitors;
import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

/**
 * The GetTermPositionVisitor collects the positions of subterms
 * equivalent to a given term
 * @author Stephan Swiderski
 * @version $Id$
 */
public class GetTermPositionsVisitor implements CoarseGrainedTermVisitor {
    private AlgebraTerm match;
    private Position currentprefix;
    private Set<Position> collector;

    /**
     * @param match the term to compare with the subterms
     * @param collector Set<Position> to which the matching positions are added
     */
    public GetTermPositionsVisitor(AlgebraTerm match,Set<Position> collector){
       this.currentprefix = Position.create();
       this.match = match;
       this.collector = collector;
    }

    /**
     * @param prefix all matching positions are append to this prefix (could be destoryed)
     * @param match the term to compare with the subterms
     * @param collector Set<Position> to which the matching positions are added
     */
    public GetTermPositionsVisitor(Position prefix,AlgebraTerm match,Set<Position> collector){
       this.currentprefix = prefix;
       this.match = match;
       this.collector = collector;
    }

    @Override
    public Object caseVariable(AlgebraVariable v) {
    //System.out.println("#" + match.toString() + " -- " + ((Term)v).toString());
        if (this.match.equals((AlgebraTerm)v)) {
       this.collector.add(this.currentprefix);
    }
    return null;
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {
    //System.out.println("#" + match.toString() + " -- " + ((Term)f).toString());
        if (this.match.equals((AlgebraTerm)f)) {
           //System.out.println(".");
        this.collector.add(this.currentprefix);
    } else {
        Position prefix = this.currentprefix;
           //System.out.println(":");
        List<AlgebraTerm> args = f.getArguments();
        for (int i=0;i<args.size();i++){
            this.currentprefix = prefix.shallowcopy();
            this.currentprefix.add(i);
        ((AlgebraTerm) args.get(i)).apply(this);
        }
    }
    return null;
    }


}
