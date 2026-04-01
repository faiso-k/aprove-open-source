package aprove.verification.dpframework.BasicStructures.Unification;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;

/**
 * Basis implementation of a node in a TermPairDag.
 *
 * @author Matthias Sondermann
 * @version $Id$
 */
public abstract class TermPairDagNode<N extends TermPairDagNode> implements Exportable{

    private final int hashCode;
    
    /**
     * term which is represented at this node
     */
    protected TRSTerm term;
    /**
     * list of all children in the dag
     */
    protected List<N> children;
    /**
     *  list of all fathers in the dag
     */
    protected List<N> fathers;

    /**
     * only for dot-output to distinguish between two nodes
     * with same function symbol and different arity
     */
    protected int nodeNumber;
    private static int nodeCounter = 0;

    public TermPairDagNode(TRSTerm term) {
        if(Globals.useAssertions){
            assert(term!=null);
        }
        this.term = term;
        this.children = new ArrayList<N>();
        this.fathers = new ArrayList<N>();
        this.nodeNumber = TermPairDagNode.nodeCounter++;

        hashCode = this.getTerm().hashCode() * 6163;
    }

    /**
     * Returns the ith child of the node
     */
    public N getChild(int i) {
        return this.children.get(i);
    }

    public List<N> getChildren() {
        return this.children;
    }

    public List<N> getFathers() {
        return this.fathers;
    }

    public void addChild(N child) {
        this.children.add(child);
    }

    public void addFather(N father) {
        this.fathers.add(father);
    }

    public TRSTerm getTerm() {
        return this.term;
    }

    public void setTerm(TRSTerm term) {
        this.term = term;
    }

    public boolean isFunctionNode() {
        return !this.term.isVariable();
    }

    public boolean isVariableNode() {
        return this.term.isVariable();
    }

    public boolean isConstantNode() {
        if(!this.isVariableNode()){
            TRSFunctionApplication f = (TRSFunctionApplication) this.getTerm();
            if(f.getRootSymbol().getArity()==0) {
                return true;
            }
        }
        return false;
    }

    public String getUniqueName() {
        if(this.term.isVariable()) {
            return ((TRSVariable)this.term).getName();
        }
        // prints f3, g6, ...
        return ((TRSFunctionApplication)this.term).getRootSymbol().getName() + this.nodeNumber;
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
            TermPairDagNode that = (TermPairDagNode) other;
            if(this.getTerm().equals(that.getTerm())){
                return true;
            }
        }
        return false;
    }

    @Override
    public String export(Export_Util eu) {
        if(this.term.isVariable()){
            return ((TRSVariable)this.term).getName();
        }
        final int outputStyle = 3;
        // prints f3, g6, ...
        if(outputStyle == 1) {
            return ((TRSFunctionApplication)this.term).getRootSymbol().getName() + this.nodeNumber;
        }
        // prints f, g, ...
        if(outputStyle == 2) {
            return ((TRSFunctionApplication)this.term).getRootSymbol().getName();
        }
        // prints f(x,y), g(a,h(x)), ...
        if(outputStyle == 3) {
            return this.getTerm().toString();
        }
        // this should never happen
        return null;
    }

    @Override
    public String toString(){
        return this.export(new PLAIN_Util());
    }
}
