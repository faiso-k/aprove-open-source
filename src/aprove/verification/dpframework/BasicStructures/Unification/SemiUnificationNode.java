package aprove.verification.dpframework.BasicStructures.Unification;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Matthias Sondermann
 * @version $Id$
 */
public class SemiUnificationNode extends TermPairDagNode<SemiUnificationNode> {

    private final int hashCode;
    
    /**
     * Triple which indicates the class representative for this node and two weights,
     * a source cost and a target cost.
     */
    private LinkTriple classRep;
    /**
     * Indicates the size of the class when the node is a class representative
     */
    private int size;
    /**
     * Indicates the presence of a self-loop
     */
    private boolean selfLoop;
    /**
     *
     */
    private int order;
    /**
     * Helper for cycle check
     */
    private boolean processed;
    private boolean inStack;
    private int cycleCost;
    private Pair<Integer,Integer> selfLoopWeights;
    /**
     * Indicates the functional symbol in this node, it is null if the node
     * represents a variable. Later it is used to represent the function symbol
     * of the equivalence class.
     */
    private SemiUnificationNode func;

    private List<LinkTriple> solExtractList;

    public SemiUnificationNode(TRSTerm term) {
        super(term);
        this.classRep = null;
        this.size = 1;
        this.selfLoop = false;
        this.processed = false;
        this.inStack = false;
        this.cycleCost = 0;
        this.selfLoopWeights = new Pair<Integer,Integer>(0,0);
        this.solExtractList = null;
        this.order = -1;
        
        this.hashCode = this.getTerm().hashCode() * 317 + this.nodeNumber * 17;

        if(term.isVariable()) {
            this.func = null;
        }
        else {
            this.func = this;
        }
    }

    public SemiUnificationNode getFunc() {
        return this.func;
    }

    public void setFunc(SemiUnificationNode func) {
        this.func = func;
    }

    public void setOrder(int order) {
        this.order = order;
    }

    public int getOrder() {
        return this.order;
    }

    public boolean isSelfLoop() {
        return this.selfLoop;
    }

    public void setSelfLoop(boolean selfLoop) {
        this.selfLoop = selfLoop;
    }

    public int getSize() {
        return this.size;
    }

    public void setSize(int size) {
        this.size = size;
    }

    public LinkTriple getClassRep() {
        return this.classRep;
    }

    public void setClassRep(LinkTriple linkTriple) {
        this.classRep = linkTriple;
    }

    public boolean isProcessed() {
        return this.processed;
    }

    public void setProcessed(boolean processed) {
        this.processed = processed;
    }

    public boolean isInStack() {
        return this.inStack;
    }

    public void setInStack(boolean inStack) {
        this.inStack = inStack;
    }

    public int getCycleCost() {
        return this.cycleCost;
    }

    public void setCycleCost(int cycleCost) {
        this.cycleCost = cycleCost;
    }

    public Pair<Integer, Integer> getSelfLoopWeights() {
        return this.selfLoopWeights;
    }

    public void setSelfLoopWeights(Pair<Integer, Integer> selfLoopWeights) {
        this.selfLoopWeights = selfLoopWeights;
    }

    public List<LinkTriple> getSolExtractList() {
        return this.solExtractList;
    }

    public void setSolExtractList(List<LinkTriple> solExtractList) {
        this.solExtractList = solExtractList;
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    @Override
    public boolean equals(Object other) {
        if(this == other) {
            return true;
        }
        if(other == null) {
            return false;
        }
        if(other instanceof TermPairDagNode) {
            SemiUnificationNode that = (SemiUnificationNode) other;
            if(this.getTerm().equals(that.getTerm()) && (this.nodeNumber == that.nodeNumber)){
                return true;
            }
        }
        return false;
    }
}
