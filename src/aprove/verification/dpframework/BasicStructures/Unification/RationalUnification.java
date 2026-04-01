package aprove.verification.dpframework.BasicStructures.Unification;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.EquivalenceClass.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * debug: DEBUG_SPECIALMAN
 *
 * @author Matthias Sondermann
 * @version $Id$
 *
 * Implementation of an extended version of the Paterson-Wegmann unification algorithm for
 * rational unification. For more details have a look at the description of the implementation
 * "How the Paterson-Wegman unification algorithm works" which I wrote.
 */
public class RationalUnification {
    /**
     * The two terms which are tried to unify
     */
    private TRSTerm term1;
    private TRSTerm term2;
    /**
     * Variables which are not allowed to be instantiated infintely
     */
    private Set<TRSVariable> finiteVars;
    /**
     * Variables which must be instantiated infinitely to unify the two given terms
     */
    private Set<TRSVariable> infiniteVars;
    /**
     * The dag (with full sharing) which contains the two terms
     */
    private RationalUnificationDag dag;
    /**
     * Small helper to simplify handling the different states of the algorithm
     */
    private enum ToDo {
        GO_ON_TRUE,
        GO_ON_FALSE;
    }
    /**
     * Only for debugging
     */
    private static final boolean deepDebug = false;

    /**
     * This constructor should be used when a new unification problem is to solve.
     * @param finiteVars These variables must be instantiated finitely. If some variable
     *                   must be instantiated infinitely to unify the two terms
     *                   the algorithm returns false
     */
    public RationalUnification(TRSTerm term1, TRSTerm term2, Set<TRSVariable> finiteVars){
        if(Globals.useAssertions){
            assert(term1 != null && term2 != null);
        }
        this.initFields(term1, term2, finiteVars);
    }

    /**
     * This constructor should be used when an already existing unification problem must be restarted
     * @param startEquivNodes the nodes which are already computed by the last iteration
     */
    public RationalUnification(TRSTerm term1, TRSTerm term2, Set<TRSVariable> finiteVars, Set<Pair<RationalUnificationNode, RationalUnificationNode>> startEquivNodes){
        if(Globals.useAssertions){
            assert(term1 != null && term2 != null);
        }
        this.initFields(term1, term2, finiteVars);
        for(Pair<RationalUnificationNode, RationalUnificationNode> pair  : startEquivNodes) {
            this.dag.addEquivEdge(pair.x.getTerm(), pair.y.getTerm());
        }
    }

    /**
     * Does what you think ;-)
     */
    private void initFields(TRSTerm term1, TRSTerm term2, Set<TRSVariable> finiteVars) {
        this.term1 = term1;
        this.term2 = term2;
        this.finiteVars = finiteVars;
        this.infiniteVars = new LinkedHashSet<TRSVariable>();
        this.dag = new RationalUnificationDag(term1,term2);
    }

    /**
     * Tries to unify term1 and term2.
     * @return (true, set) if the two terms unify rational under the condition that the variables of
     *                     the set must be instantiated infinitely
     *         (false, null) otherise
     */
    public Pair<Boolean, Set<TRSVariable>> unify() {
        // trivial unification
        if(this.term1.equals(this.term2)) {
            return new Pair<Boolean, Set<TRSVariable>>(true, new HashSet<TRSVariable>());
        }
        // add equivalent edge between the two roots
        this.dag.addEquivEdge(this.term1,this.term2);
        // run function finish with every not completed node representing a function node
        for(RationalUnificationNode funcNode: this.dag.getFunctionNodes()) {
            if(!funcNode.isCompleted()) {
                if(!this.finish(funcNode)) {
                    return new Pair<Boolean, Set<TRSVariable>>(false, null);
                }
            }
        }
        // there are only uncompleted nodes left representing a variable
        // run function finish with every not completed node representing a variable node
        for(RationalUnificationNode varNode: this.dag.getVariableNodes()) {
            if(!varNode.isCompleted()) {
                if(!this.finish(varNode)) {
                    return new Pair<Boolean, Set<TRSVariable>>(false, null);
                }
            }
        }
        // no failure found and all nodes are completed -> terms unify
        if(Globals.DEBUG_SPECIALMAN) {
            assert(this.checkFinAndInfinSets());
        }
        return new Pair<Boolean, Set<TRSVariable>>(true, this.infiniteVars);
    }

    /**
     * Checks if the equivalence class of <code>r</code> can be constructed conflict free.
     */
    private boolean finish(RationalUnificationNode r) {
        // In the original algorithm you have to check if r is completed but this is done
        // in every case before calling this funtion with r to speed up the algorithm.
        if(Globals.DEBUG_SPECIALMAN && RationalUnification.deepDebug) {
            System.out.println("debug rat_unif: finish with " + r);
        }
        if(r.getEquivalenceClass() != null) {
            // "occur check case 1"
            // Since r as a father of node and the node itself are in the same equivalence class
            // normally the occur check would fail, but here we have to analyse the class to know
            // how we have to go on.
            ToDo status = this.checkClass(r.getEquivalenceClass());
            if(status == ToDo.GO_ON_FALSE) {
                GO_ON_FALSE :    return false;
            }
        }
        else {
            // r is no member of an equivalence class so create a new one
            // with r as its representative
            new EquivalenceClass(r);
        }
        // Set pointer to itself
        EquivalenceClass actualEquivalenceClass = r.getEquivalenceClass();

        Stack<RationalUnificationNode> stack = new Stack<RationalUnificationNode>();
        stack.push(r);

        while(!stack.isEmpty()) {
            RationalUnificationNode s = stack.pop();

            if(this.symbolsClash(r, s)) {
                return false;
            }
            // Run finish with all fathers, so that they are definetely completed before
            // the actual node is completed
            for(RationalUnificationNode father: s.getFathers()) {
                if(!father.isCompleted()) {
                    // If finish returns false the whole unification fails
                    if(!this.finish(father)) {
                        return false;
                    }
                }
            }

            // Get all equivalent nodes of s.
            // (Iterate over a copy because it is possible that some new links are added
            // during the computation of a father)
            Set<RationalUnificationNode> sCopy = new LinkedHashSet<RationalUnificationNode>(s.getEquivNodes());
            for(RationalUnificationNode t: sCopy) {
                if(t == r) {
                     // Nothing to do here, as t is already visited
                    continue;
                }
                if(t.getEquivalenceClass() == null) {
                    // Add t to the actual equivalence class
                    boolean newInfin = actualEquivalenceClass.add(t);
                    if(newInfin) {
                        this.infiniteVars.add((TRSVariable) t.getTerm());
                    }
                    stack.push(t);
                }
                else if(t.getEquivalenceClass() != actualEquivalenceClass) {
                    if(Globals.DEBUG_SPECIALMAN) {
                        System.out.println("debug rat_unif: merge (old) " + t.getEquivalenceClass() +
                                           " and\n                      (new) " + actualEquivalenceClass);
                    }
                    // "occur check - case 2"
                    // The two classes have to be merged and the resulting class must be checked again.
                    // If the actual class is represented by a variable and the class of t by
                    // a function application the new representative must be the function application
                    // so that the members of the actual class must be added into the class of t.
                    // Of course the actual equivalence class is now the merged class with the function
                    // application as its representative.
                    Pair<EquivalenceClass, ToDo> pair = this.mergeClasses(actualEquivalenceClass, t.getEquivalenceClass());
                    actualEquivalenceClass = pair.x;
                    ToDo nextToDo = pair.y;
                    if(nextToDo == ToDo.GO_ON_FALSE) {
                     return false;
                    }
                }
            }
            // Now check if the equivalence has to be propagated to the children.
            // The case that the actual equivalence class is the result of merging
            // nothing happens here because r and s must be variables
            if(s != r) {
                if(!s.getTerm().isVariable()) {
                    for(int i=0; i < s.getChildren().size(); i++) {
                        // Add equivalent edges between the children of s and r
                        this.dag.addEquivEdge(s.getChild(i),r.getChild(i));
                    }
                }
                s.setCompleted(true);
            }
        }
        r.setCompleted(true);
        // Finish with node r was succesfull
        return true;
    }

    /**
     * Does what you think ;-)
     * @return true iff the rott symbols are different
     */
    private boolean symbolsClash(RationalUnificationNode one, RationalUnificationNode two) {
        if(one.isFunctionNode() && two.isFunctionNode()) {
            FunctionSymbol fOne = ((TRSFunctionApplication) one.getTerm()).getRootSymbol();
            FunctionSymbol fTwo = ((TRSFunctionApplication) two.getTerm()).getRootSymbol();
            if(! fOne.equals(fTwo)) {
                // failure: symbols clash!
                if(Globals.DEBUG_SPECIALMAN) {
                    System.out.println("debug rat_unif: symbol clash of " + fOne + " and " + fTwo);
                }
                return true;
            }
        }
        return false;
    }

    /**
     * Checks the status from the given class and says what to do next
     */
    private ToDo checkClass(EquivalenceClass eClass) {
        ClassStatus status = eClass.getClassStatus(this.finiteVars);
        switch(status) {
        case SYMBOL_CLASH :     // Since there are two different function symbols in one class
                                return ToDo.GO_ON_FALSE;
        case VARIABLE_CONFLICT :// Some given finite variable has to be instantiated infinitely
                                return ToDo.GO_ON_FALSE;
        case INFINITE :          // If a unify-call returns false the variables should not be added
                                if(this.infiniteVars != null) {
                                    this.infiniteVars.addAll(eClass.getVariablesOfEquivalenceClass());
                                }
                                // Connect all children of all function nodes with the children
                                // of the representative
                                RationalUnificationNode rep = eClass.getRepresentative();
                                for(RationalUnificationNode n : eClass.getFunctionNodesOfEquivalenceClass()) {
                                    ToDo toDo = this.makeChildrenEquivalent(rep, n);
                                    if(toDo == ToDo.GO_ON_FALSE) {
                                        return ToDo.GO_ON_FALSE;
                                    }
                                }
                                // go on
                                return ToDo.GO_ON_TRUE;
        case FINITE :             // nothing to do here
                                return ToDo.GO_ON_TRUE;
        }
        // Should never happen
        return null;
    }

    /**
     * Connects the i-th child of one with the i-th child of two if both are function applications.
     * In case of variables nothing happens. An exception is thrown if the rott symbols differ.
     */
    private ToDo makeChildrenEquivalent(RationalUnificationNode one, RationalUnificationNode two) {
        // no edge at the same node
        if(one.equals(two)) {
            return ToDo.GO_ON_TRUE;
        }
        if(one.isFunctionNode() && two.isFunctionNode()) {
            FunctionSymbol fOne = ((TRSFunctionApplication) one.getTerm()).getRootSymbol();
            FunctionSymbol fTwo = ((TRSFunctionApplication) two.getTerm()).getRootSymbol();
            if(fOne.equals(fTwo)) {
                for(int i=0; i < one.getChildren().size(); i++) {
                    // Add equivalent edges between the children of one and two
                    this.dag.addEquivEdge(one.getChild(i),two.getChild(i));
                    // System.out.println("adding " + one.getChild(i) + " and " + two.getChild(i));
                }
                return ToDo.GO_ON_TRUE;
            }
            else {
                // Symbol clash!
                return ToDo.GO_ON_FALSE;
            }
        }
        // one and/or two is a variable
        return ToDo.GO_ON_TRUE;
    }

    /**
     * Merges the two given equivalence classes, the representative from the class one
     * will be the representative of the merged class
     */
    private Pair<EquivalenceClass, ToDo> mergeClasses(EquivalenceClass one, EquivalenceClass two) {
        EquivalenceClass newClass = null;
        RationalUnificationNode newRep = null;
        if(one.isVariableClass() && two.isVariableClass()) {
            newRep = two.getRepresentative();
            for(RationalUnificationNode node : one.getMembers()) {
                // since one does not contain any function application no children must be
                // made equivalent because every member of class one is a variable
                boolean newInfin = two.add(node);
                if(newInfin) {
                    this.infiniteVars.add((TRSVariable) node.getTerm());
                }
            }
            if(Globals.DEBUG_SPECIALMAN) {
                System.out.println("debug rat_unif: merge with representative of old class");
            }
            newClass = two;
        }
        else {
            newRep = one.getRepresentative();
            for(RationalUnificationNode node : two.getMembers()) {
                // since the children of node and the representative of one were made equivalent
                // we now have to make the children of node and the representative of two equivalent
                ToDo t = this.makeChildrenEquivalent(newRep, node);
                if(t == ToDo.GO_ON_FALSE) {
                    return new Pair<EquivalenceClass, ToDo>(null, ToDo.GO_ON_FALSE);
                }
                boolean newInfin = one.add(node);
                if(newInfin) {
                    this.infiniteVars.add((TRSVariable) node.getTerm());
                }
            }
            this.dag.addEquivEdge(one.getRepresentative(), two.getRepresentative());
            if(Globals.DEBUG_SPECIALMAN) {
                System.out.println("debug rat_unif: merge with representative of new class");
            }
            newClass = one;
        }
        ToDo check = this.checkClass(newClass);
        return new Pair<EquivalenceClass, ToDo>(newClass, check);
    }

    public String export(Export_Util eu){
        String linesep = System.getProperty("line.separator");
        StringBuilder s = new StringBuilder();
        s.append("Rational unification problem: " + this.term1 + " =? " + this.term2 + linesep);
        long start = System.nanoTime();
        Pair<Boolean, Set<TRSVariable>> returnPair = this.unify();
        long end = System.nanoTime();
        if(returnPair.x == false) {
            s.append("These terms do not unify.\n");
        }
        else {
            s.append("These terms unify!" + linesep);
            s.append("The following variables were given to be instantiated finitely: " + this.finiteVars + linesep);
            s.append("The following variables must be instantiated infinetely: " + this.infiniteVars + linesep);
        }
        long res = (end-start)/1000000;

        s.append("It took " + res + " ms.");
        return s.toString();
    }

    @Override
    public String toString(){
        return this.export(new PLAIN_Util());
    }

    private boolean checkFinAndInfinSets() {
        for(TRSVariable v : this.finiteVars) {
            if(this.infiniteVars.contains(v)) {
                return false;
            }
        }
        return true;
    }
}
