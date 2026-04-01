package aprove.verification.idpframework.Algorithms.Unification;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;

/**
 * Basis implementation of a node in a TermPairDag.
 * @author Martin Pluecker, copied from Matthias Sondermann
 * @version $Id$
 */
public abstract class TermPairDagNode<N extends TermPairDagNode<?>> implements
        Exportable {
    /**
     * term which is represented at this node
     */
    protected ITerm<?> term;
    /**
     * list of all children in the dag
     */
    protected List<N> children;
    /**
     * list of all fathers in the dag
     */
    protected List<N> fathers;

    /**
     * only for dot-output to distinguish between two nodes with same function
     * symbol and different arity
     */
    protected int nodeNumber;
    private static int nodeCounter = 0;

    public TermPairDagNode(final ITerm<?> term) {
        if (Globals.useAssertions) {
            assert (term != null);
        }
        this.term = term;
        this.children = new ArrayList<N>();
        this.fathers = new ArrayList<N>();
        this.nodeNumber = TermPairDagNode.nodeCounter++;
    }

    /**
     * Returns the ith child of the node
     */
    public N getChild(final int i) {
        return this.children.get(i);
    }

    public List<N> getChildren() {
        return this.children;
    }

    public List<N> getFathers() {
        return this.fathers;
    }

    public void addChild(final N child) {
        this.children.add(child);
    }

    public void addFather(final N father) {
        this.fathers.add(father);
    }

    public ITerm<?> getTerm() {
        return this.term;
    }

    public void setTerm(final ITerm<?> term) {
        this.term = term;
    }

    public boolean isFunctionNode() {
        return !this.term.isVariable();
    }

    public boolean isVariableNode() {
        return this.term.isVariable();
    }

    public boolean isConstantNode() {
        if (!this.isVariableNode()) {
            final IFunctionApplication<?> f =
                (IFunctionApplication<?>) this.getTerm();
            if (f.getRootSymbol().getArity() == 0) {
                return true;
            }
        }
        return false;
    }

    public String getUniqueName() {
        if (this.term.isVariable()) {
            return ((IVariable<?>) this.term).getName();
        }
        // prints f3, g6, ...
        return ((IFunctionApplication<?>) this.term).getRootSymbol().getName()
            + this.nodeNumber;
    }

    @Override
    public int hashCode() {
        return this.term.hashCode();
    }

    @Override
    public boolean equals(final Object other) {
        if (this == other) {
            return true;
        }
        if (other == null) {
            return false;
        }
        if (other instanceof TermPairDagNode<?>) {
            final TermPairDagNode<?> that = (TermPairDagNode<?>) other;
            if (this.getTerm().equals(that.getTerm())) {
                return true;
            }
        }
        return false;
    }

    @Override
    public String export(final Export_Util eu) {
        if (this.term.isVariable()) {
            return ((IVariable<?>) this.term).getName();
        }
        /*
        final int outputStyle = 3;
        // prints f3, g6, ...
        if(outputStyle == 1) {
            return ((IFunctionApplication<?>)term).getRootSymbol().getName() + this.nodeNumber;
        }
        // prints f, g, ...
        if(outputStyle == 2) {
            return ((IFunctionApplication<?>)term).getRootSymbol().getName();
        }
        // prints f(x,y), g(a,h(x)), ...
        if(outputStyle == 3) {
            return this.getTerm().toString();
        }
        */
        // this should never happen
        return this.getTerm().export(eu);
    }

    @Override
    public final String toString() {
        return this.export(new PLAIN_Util());
    }
}
