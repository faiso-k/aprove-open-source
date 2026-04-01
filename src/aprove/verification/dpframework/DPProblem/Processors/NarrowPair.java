package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.Processors.NonTerminationProcessor.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Class which represents a pair of terms which stores the way of narrowings
 * you have to use to narrow from <code>pair.x</code> to <code>pair.y</code>.
 *
 * @author Matthias Sondermann
 */
@SuppressWarnings("serial")
public class NarrowPair extends Pair<TRSTerm,TRSTerm>{

    Direction narrowDir;
    private List<Triple<Rule,Position,Trs>> narrowList;
    private List<Pair<Position,Rule>> rewriteSeq; //Used for Probabilistic reconstruction of the loop
    private Map<Rule,Integer> numOfAppl;

    // only for proof
    Rule dp;

    /**
     * constructor for a narrowing pair which initializes all attributes to null even pair.x and pair.y
     */
    public NarrowPair(){
        super(null,null);
        this.narrowDir = null;
        this.narrowList = null;
        this.rewriteSeq = null;
        this.numOfAppl = null;
        this.dp = null;
    }

    /**
     * constructor for a narrowing pair (narrowRule must be non-null).
     * the rRules are used to remember how often a rule is used.
     */
    public NarrowPair(final Rule narrowRule, final Set<Rule> allRules){
        super(narrowRule.getLeft(),narrowRule.getRight());

        this.narrowDir = Direction.NONE;
        this.narrowList = new ArrayList<Triple<Rule,Position,Trs>>();
        this.rewriteSeq = new ArrayList<Pair<Position, Rule>>();
        rewriteSeq.add(new Pair<>(Position.EPSILON, narrowRule));
        this.numOfAppl = new LinkedHashMap<Rule,Integer>();
        this.dp = narrowRule;
        // initialise every rule with 0
        for(final Rule rule : allRules){
            this.numOfAppl.put(rule,0);
        }
    }

    /**
     * constructor for a narrowing pair
     */
    public NarrowPair(final TRSTerm lhs, final TRSTerm rhs, final NarrowPair parentPair, final Triple<Rule,Position,Trs> addedNarrowing, final Direction narrowDir){
        super(lhs,rhs);

        this.narrowList = new ArrayList<Triple<Rule,Position,Trs>>();
        this.rewriteSeq = new ArrayList<Pair<Position, Rule>>();
        this.numOfAppl = new LinkedHashMap<Rule,Integer>();
        this.narrowDir = narrowDir;
        this.dp = parentPair.dp;

        // copy the old narrowings to the new
        for(final Triple<Rule,Position,Trs> triple : parentPair.narrowList){
            this.narrowList.add(triple);
        }
        // copy the old rewrite sequence to the new
        for(final Pair<Position,Rule> pair : parentPair.rewriteSeq){
            this.rewriteSeq.add(pair);
        }
        // copy the old number of narrowings to the new
        for(final Map.Entry<Rule,Integer> entry : parentPair.numOfAppl.entrySet()){
            final Rule rule = entry.getKey();
            this.numOfAppl.put(rule,Integer.valueOf(entry.getValue()));
        }
        // add additional narrowing (actually this is the difference between the parentPair and the new pair
        this.narrowList.add(addedNarrowing);
        this.rewriteSeq.add(new Pair<>(addedNarrowing.y, addedNarrowing.x));
        this.numOfAppl.put(addedNarrowing.x, this.getNrOfAppls(addedNarrowing.x) + 1);
    }

    @Override
    public String toString(){
        return this.x + " ~> " + this.y;
    }

    /**
     * returns the number of applications of <code>rule</code> to the left
     */
    public int getNrOfAppls(final Rule rule){
        return this.numOfAppl.get(rule);
    }

    /**
     * returns the list of used narrowings
     */
    public List<Triple<Rule,Position,Trs>> getNarrowList(){
        return this.narrowList;
    }
    
    /**
     * returns the list of used narrowings
     */
    public ImmutableList<Pair<Position,Rule>> getRewriteSeq(){
        return ImmutableCreator.create(rewriteSeq);
    }

    /**
     * returns a pair containing the left and right term of the narrowing pair
     */
    public Pair<TRSTerm,TRSTerm> getTermPair(){
        return new Pair<TRSTerm,TRSTerm>(this.x,this.y);
    }

    public Direction getDirection() {
        return this.narrowDir;
    }

    public Pair<TRSTerm,TRSTerm> getStandardRepresentation(){
        return new Pair<TRSTerm,TRSTerm>(this.x.getStandardRenumbered(),this.y.getStandardRenumbered());
    }

    /**
     * Returns a new NarrowPair with the same attributes. This is used if
     * a semiunifying pair is found to add the first or the last narrowing.
     */
    public NarrowPair copy(){
        final NarrowPair copy = new NarrowPair();
        copy.x = this.x;
        copy.y = this.y;
        copy.dp = this.dp;
        copy.narrowDir = this.narrowDir;
        copy.narrowList = new ArrayList<Triple<Rule,Position,Trs>>(this.narrowList);
        copy.numOfAppl = new LinkedHashMap<Rule,Integer>(this.numOfAppl);
        return copy;
    }
}