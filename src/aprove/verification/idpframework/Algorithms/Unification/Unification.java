// created 25.04.2005
package aprove.verification.idpframework.Algorithms.Unification;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * debug: DEBUG_SPECIALMAN Class which contains the "Peterson-Wegman"
 * unification algorithm. Either you can check if two terms unify, or you can
 * get an mgu if such exists. It is also possible to check a problem with more
 * than two terms like (s1=?t1,...,sn=?tn). The algorithm works on a dag. This
 * dag is optimzed because common subexpressions share one node, so the dag is
 * as small as possible and the number of iterations of the algorithm is
 * reduced. If you want to have a look at the original paper be aware of the
 * error in the pseudocode! Also the paper "About the Peterson-Wegman-Algorithm"
 * has an error in the pseudocode! The method unify() is much faster than
 * getMgu(). So use unify() if are not interested in the unifier.
 * @author Martin Pluecker, copied from Matthias Sondermann
 * @version $Id$
 */
public class Unification implements Exportable {

    /**
     * do these terms unify?
     */
    private ITerm<?> term1;
    private ITerm<?> term2;
    /**
     * i hope you know what this is
     */
    private ISubstitution mgu;
    /**
     * dag which represents the two terms
     */
    private UnificationDag dag;

    /**
     * only for output
     */
    private String errorMessage;

    /**
     * helper to speed up generating mgu
     */
    private Map<IVariable<?>, ITerm<?>> finalSubstMap;

    /**
     * creates a new unification problem of the two given terms
     */
    public Unification(final ITerm<?> term1, final ITerm<?> term2) {

        if (Globals.useAssertions) {
            assert (term1 != null && term2 != null);
        }
        this.term1 = term1;
        this.term2 = term2;
        this.mgu = null;
        this.dag = new UnificationDag(term1, term2);
        this.errorMessage = "";
    }

    /**
     * creates a new unification problem of the given set of term pairs
     */
    public Unification(final Set<Pair<ITerm<?>, ITerm<?>>> termPairSet,
        final IDPPredefinedMap predefinedMap) {
        // uniform case
        if (termPairSet.size() == 1) {
            for (final Pair<ITerm<?>, ITerm<?>> termPair : termPairSet) {
                this.term1 = termPair.x;
                this.term2 = termPair.y;
            }
            this.dag = new UnificationDag(this.term1, this.term2);
        } else {
            final int size = termPairSet.size();
            final IFunctionSymbol<?> f =
                IFunctionSymbol.create("newRoot", size, predefinedMap);
            final ArrayList<ITerm<?>> argsTerm1 = new ArrayList<ITerm<?>>(size);
            final ArrayList<ITerm<?>> argsTerm2 = new ArrayList<ITerm<?>>(size);
            for (final Pair<ITerm<?>, ITerm<?>> termPair : termPairSet) {
                argsTerm1.add(termPair.x);
                argsTerm2.add(termPair.y);
            }
            this.term1 =
                ITerm.createFunctionApplication(f,
                    ImmutableCreator.create(argsTerm1));
            this.term2 =
                ITerm.createFunctionApplication(f,
                    ImmutableCreator.create(argsTerm2));
            this.dag = new UnificationDag(this.term1, this.term2);
        }
    }

    /**
     * Calls the unification algorithm if needed and returns an mgu if such
     * exists.
     * @return An mgu if such exists, else null
     */
    public ISubstitution getMgu() {
        // if the mgu is already computed return it
        if (this.mgu != null) {
            return this.mgu;
        }

        // trivial unification
        if (this.term1.equals(this.term2)) {
            this.mgu = ISubstitution.emptySubstitution();
            return this.mgu;
        }

        // generate mgu only if the terms unify
        if (this.unify()) {
            this.buildFinalSubst();
        }
        // be sure that the mgu really makes thes terms equal
        if (Globals.useAssertions) {
            assert (this.checkPropernessOfMgu());
        }
        return this.mgu;
    }

    /**
     * Checks if the two given terms unify. This is much faster than running
     * this.getMgu(). So use this if you do not need the mgu.
     * @return true if the terms unify, else false
     */
    public boolean unify() {
        // trivial unification
        if (this.term1.equals(this.term2)) {
            return true;
        }

        // add equivalent edge between the two roots
        this.dag.addEquivEdge(this.term1, this.term2);

        // run function finish with every not completed node representing a function node
        for (final UnificationNode funcNode : this.dag.getFunctionNodes()) {
            if (!funcNode.isCompleted()) {
                if (!this.finish(funcNode)) {
                    return false;
                }
            }
        }
        // there are only uncompleted nodes left representing a IVariable<?>
        // run function finish with every not completed node representing a IVariable<?> node
        for (final UnificationNode varNode : this.dag.getVariableNodes()) {
            if (!varNode.isCompleted()) {
                if (!this.finish(varNode)) {
                    return false;
                }
            }
        }
        // no failure found and all nodes are completed -> terms unify
        return true;
    }

    /**
     * main method of the "Peterson-Wegman"-algorithm
     * @param actual node which is to complete
     * @return true if the node could be completed, else false
     */
    private boolean finish(final UnificationNode r) {
        // in the original algorithm you have to check if r is completed
        // but this is done in every case before calling this funtion with r to speed up the
        // algorithm.
        if (r.getPointer() != null) {
            // failure if pointer is already defined
            if (Globals.DEBUG_SPECIALMAN) {
                if (this.errorMessage.equals("")) {
                    this.errorMessage = "Looping detected";
                }
            }
            return false;
        }
        // set pointer to itself
        r.setPointer(r);

        final Stack<UnificationNode> stack = new Stack<UnificationNode>();
        stack.push(r);

        while (!stack.isEmpty()) {
            final UnificationNode s = stack.pop();

            if (r.isFunctionNode() && s.isFunctionNode()) {
                // check for symbol clash
                final IFunctionSymbol<?> f1 =
                    ((IFunctionApplication<?>) r.getTerm()).getRootSymbol();
                final IFunctionSymbol<?> f2 =
                    ((IFunctionApplication<?>) s.getTerm()).getRootSymbol();
                if (!f1.equals(f2)) {
                    // failure: Symbol clash!
                    if (Globals.DEBUG_SPECIALMAN) {
                        if (this.errorMessage.equals("")) {
                            this.errorMessage =
                                "Symbol clash occured (between " + f1.getName()
                                + " and " + f2.getName() + ")";
                        }
                    }
                    return false;
                }
            }
            // no clash found

            // run finish with all fathers, so that they are definetely completed before
            // the actual node is completed
            for (final UnificationNode father : s.getFathers()) {
                if (!father.isCompleted()) {
                    // if finish returns false the whole unification fails
                    if (!this.finish(father)) {
                        return false;
                    }
                }
            }

            // get all equivalent nodes of s
            for (final UnificationNode t : s.getEquivNodes()) {
                // If t is already member of the actual equivalence class
                // nothing is to be done
                // (The authors of the paper "About the Paterson-Wegman
                // Linear Unification Algorithm" add "t.isCompleted" to the first
                // if-case which is not necessary)
                if (t == r) {
                    continue;
                }
                if (t.getPointer() == null) {
                    // pointer of t is undefined so set it to r
                    t.setPointer(r);
                    stack.push(t);
                } else if (t.getPointer() != r) {
                    // loop failure
                    if (Globals.DEBUG_SPECIALMAN) {
                        if (this.errorMessage.equals("")) {
                            this.errorMessage = "Classification problem";
                        }
                    }
                    return false;
                }
            }
            // s and r are different nodes so substitute (this is done after finish if required)
            // if s is a IVariable<?> or decompose
            if (s != r) {
                if (!s.getTerm().isVariable()) {
                    for (int i = 0; i < s.getChildren().size(); i++) {
                        // add equivalent edges between the children of s and r
                        this.dag.addEquivEdge(s.getChild(i), r.getChild(i));
                    }
                } else {
                    final IVariable<?> sVar = (IVariable<?>) s.getTerm();
                    final boolean domainConflict;
                    if (!sVar.getDomain().isSpecialization(
                        r.getTerm().getDomain())) {
                        domainConflict =
                            !r.getTerm().isVariable()
                            || !r.getTerm().getDomain().isSpecialization(
                                s.getTerm().getDomain());
                    } else {
                        domainConflict = false;
                    }
                    if (domainConflict) {
                        if (Globals.DEBUG_SPECIALMAN) {
                            if (this.errorMessage.equals("")) {
                                this.errorMessage = "Type problem";
                            }
                        }
                        return false;
                    }
                }
                s.setCompleted(true);
            }
        }
        r.setCompleted(true);
        // finish with node r was succesfull
        return true;
    }

    /**
     * Because the unification algorithm creates no substitution, this has to be
     * made here using the equivalent edges in the dag which exist after running
     * the unification algorithm
     * @return the final substitution
     */
    private void buildFinalSubst() {
        this.finalSubstMap = new LinkedHashMap<IVariable<?>, ITerm<?>>();
        for (final UnificationNode varNode : this.dag.getVariableNodes()) {
            final IVariable<?> actVar = (IVariable<?>) varNode.getTerm();
            if (!this.finalSubstMap.containsKey(actVar)) {
                this.finalSubstMap.put(actVar,
                    this.getFinalTermForTerm(varNode));
            }
        }
        this.mgu =
            ISubstitution.create(ImmutableCreator.create(this.finalSubstMap));
    }

    /**
     * @param termNode actual node for which a substitution term is needed
     * @return the term at termNode has to be substituted with this term
     */
    private ITerm<?> getFinalTermForTerm(final UnificationNode termNode) {
        // check if it is already computed
        if (termNode.getSubstTerm() != null) {
            return termNode.getSubstTerm();
        }
        if (termNode.getPointer() != termNode) {
            final ITerm<?> substTerm = this.getFinalTermForTerm(termNode.getPointer());
            termNode.setSubstTerm(substTerm);
            return substTerm;
        } else if (termNode.isVariableNode()) {
            final IVariable<?> var = (IVariable<?>) termNode.getTerm();
            termNode.setSubstTerm(var);
            this.finalSubstMap.put(var, var);
            return termNode.getTerm();
        } else {
            // if termNode is a function node than return the term
            // which it is representing with all IVariable<?>s substituted
            final IFunctionApplication<?> fapp =
                (IFunctionApplication<?>) termNode.getTerm();
            final IFunctionSymbol<?> f = fapp.getRootSymbol();
            final ArrayList<ITerm<?>> args =
                new ArrayList<ITerm<?>>(termNode.getChildren().size());
            for (final UnificationNode childNode : termNode.getChildren()) {
                args.add(this.getFinalTermForTerm(childNode));
            }
            // remember that this term has been computed
            termNode.setSubstTerm(ITerm.createFunctionApplication(f,
                ImmutableCreator.create(args)));
            return termNode.getSubstTerm();
        }
    }

    private boolean checkPropernessOfMgu() {
        if (this.mgu != null) {
            final ITerm<?> newTerm1 = this.term1.applySubstitution(this.mgu);
            final ITerm<?> newTerm2 = this.term2.applySubstitution(this.mgu);
            return newTerm1.equals(newTerm2);
        }
        return true;
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder s = new StringBuilder();
        s.append("Unification problem: " + this.term1 + " =? " + this.term2 + "\n\n");

        final ISubstitution mgu = this.getMgu();
        if (mgu == null) {
            s.append("These terms do not unify.\n");
            s.append("Error message: " + this.errorMessage);
        } else {
            s.append("These terms unify with the following mgu:\n\n");
            s.append(mgu.export(eu));
        }
        return s.toString();
    }

    @Override
    public final String toString() {
        return this.export(new PLAIN_Util());
    }

    /**
     * @return the actual state of the DAG
     */
    public String getDotOfDag() {
        return this.dag.toDOT();
    }
}
