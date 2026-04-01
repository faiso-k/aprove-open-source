package aprove.verification.theoremprover.TerminationVerifier;

import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * This class represents a node in a dependency graph.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public class DpNode extends Node<Rule> {

    public static final int NARROWING = 0;
    public static final int REWRITING = DpNode.NARROWING + 1;
    public static final int INSTANTIATION = DpNode.REWRITING + 1;
    public static final int FWDINSTANTIATION = DpNode.INSTANTIATION + 1;

    /**
     * The number of times refinements have been applied
     * to the dependency pair associated with this node.
     */
    protected int[] numOf = {0, 0, 0, 0};

    /**
     * Has this node been foward instantiated?
     */
    public boolean is_fwdinstantiated = false;

    /**
     * Has this node been instantiated?
     */
    public boolean is_instantiated = false;

    /**
     * Has this node been instantiated?
     */
    public boolean is_narrowed = false;

  /**
   * Has rewriting be done already
   */
    protected boolean has_been_rewritten = false;

    /**
     * A label for the node.
     */
    protected int label = 0;

    /**
     * The defined function symbol that the left tuple
     * symbol originated from.
     */
    protected DefFunctionSymbol origin;

    /**
     * Creates a node with a given dependency pair.
     * @param rule The dependency pair to associate with this node.
     */
    public DpNode(Rule rule) {
        super(rule);
        this.origin = null;
    }

    /**
     * Creates a node with a given dependency pair.
     * @param rule The dependency pair to associate with this node.
     * @param old The old dp graph node.
     * @param type The reason this node exists.
     */
    public DpNode(Rule rule, DpNode old, int type) {
        this(rule);
        this.numOf = new int[old.numOf.length];
        System.arraycopy(old.numOf, 0, this.numOf, 0, old.numOf.length);
        this.numOf[type]++;
    this.is_fwdinstantiated = (type == DpNode.FWDINSTANTIATION) || old.is_fwdinstantiated;
    this.is_instantiated = (type == DpNode.INSTANTIATION) || old.is_instantiated;
    this.is_narrowed = (type == DpNode.NARROWING) || old.is_narrowed;
    this.label = old.label;
    }

    /**
     * Creates a node with a given dependency pair having the same values as the old Node
     * @param rule The dependency pair to associate with this node.
     * @param old The old dp graph node.
     */
    public DpNode(Rule rule, DpNode old) {
        this(rule);
        this.numOf = new int[old.numOf.length];
        System.arraycopy(old.numOf, 0, this.numOf, 0, old.numOf.length);
        this.is_fwdinstantiated = old.is_fwdinstantiated;
        this.is_instantiated = old.is_instantiated;
        this.is_narrowed = old.is_narrowed;
        this.label = old.label;
        this.origin = old.origin;
        this.has_been_rewritten = old.has_been_rewritten;
    }


    /**
     * Return the number a certain refinement has been used.
     * @param type The type of refinement.
     */
    public int getNumOf(int type) {
        return this.numOf[type];
    }

    /**
     * Get the defined function symbol that the left tuple
     * symbol originated from.
     */
    public DefFunctionSymbol getOrigin() {
        if (this.origin == null) {
            Rule dp = (Rule)this.getObject();
        SyntacticFunctionSymbol fun = (SyntacticFunctionSymbol)dp.getLeft().getSymbol();
        if(!(fun instanceof TupleSymbol)) {
        /* DPs without tuple symbols. */
        //System.out.println("class of origin: " + fun.getClass().getName());
        this.origin = (DefFunctionSymbol)fun;
        }
        else {
        /* DPs using tuple symbols. */
                TupleSymbol tuple = (TupleSymbol)fun;
                this.origin = tuple.getOrigin();
        }
        }
        return this.origin;
    }

    public void setLabel(int l) {
    this.label = l;
    }

    public int getLabel() {
    return this.label;
    }

/**
 * Denote that the DP has been rewritten
 */    public void setHaveRewritten() {
        this.has_been_rewritten = true;
    }

    /**
     * Check whether DP has been rewritten
     */
    public boolean isAlreadyRewritten() {
        return this.has_been_rewritten;
    }
}
