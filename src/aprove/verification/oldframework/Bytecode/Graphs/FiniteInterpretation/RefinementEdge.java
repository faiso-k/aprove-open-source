package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import immutables.*;

/**
 * Representation of information about variables we gather when drawing a
 * refinement edge.
 *
 * @author Marc Brockschmidt
 */
public class RefinementEdge extends RefinementOrSplitEdge {
    /**
     * Unique ID used for serialization.
     */
    private static final long serialVersionUID = -2240094613067592043L;

    /**
     * The renaming performed in this refinement.
     */
    private final ImmutableMap<AbstractVariableReference, AbstractVariableReference> refRenaming;

    /**
     * Possible label for this edge.
     */
    private String label;

    /**
     * If this refinement is in a loop, and this field is set to true we will not enforce merging after the iteration
     */
    private final boolean doNotMergeLoop;

    /**
     * Create an edge used to connect a state with a child created through
     * refinement.
     * @param renamedR reference that was renamed.
     * @param newR new name for the renamed reference.
     */
    public RefinementEdge(final AbstractVariableReference renamedR,
            final AbstractVariableReference newR) {
        this("", renamedR, newR);
    }

    /**
     * Create an edge used to connect a state with a child created through refinement.
     * @param l Label for this edge (can be used to indicate the performed refinement)
     * @param renamedR reference that was renamed.
     * @param newR new name for the renamed reference.
     */
    public RefinementEdge(final String l,
            final AbstractVariableReference renamedR,
            final AbstractVariableReference newR) {
        this(l, Collections.singletonMap(renamedR, newR));
    }

    /**
     * Create an edge used to connect a state with a child created through refinement.
     * @param l Label for this edge (can be used to indicate the performed refinement)
     * @param refRen list of pairs of old names/new names.
     */
    public RefinementEdge(final String l,
            final Map<AbstractVariableReference, AbstractVariableReference> refRen) {
        this(l, refRen, false);
    }

    /**
     * Create an edge used to connect a state with a child created through refinement.
     * @param l Label for this edge (can be used to indicate the performed refinement)
     * @param refRen list of pairs of old names/new names.
     * @param doNotMergeLoop ff this refinement is in a loop, and this parameter is set to true we will not enforce merging after the iteration
     */
    public RefinementEdge(final String l,
            final Map<AbstractVariableReference, AbstractVariableReference> refRen,
            final boolean doNotMergeLoop) {
        this.label = l;
        this.refRenaming = ImmutableCreator.create(refRen);
        this.doNotMergeLoop = doNotMergeLoop;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getEdgeColor() {
        return "\"#99ff00\"";
    }

    /**
     * @return the label stored for this edge (might be the empty string)
     */
    @Override
    public String getLabel() {
        return this.label;
    }

    public void setLabel(String label) {
        this.label = label;
    }

    public boolean doNotMergeLoop() {
        return doNotMergeLoop;
    }

    @Override
    public String toString() {
        return this.label;
    }

    /**
     * @return the reference renaming performed in this refinement.
     */
    public ImmutableMap<AbstractVariableReference, AbstractVariableReference> getRefRenaming() {
        return this.refRenaming;
    }

    /**
     * @param varPrefix a String that is prepended to the generated variables'
     *  name.
     * @return a list of SMTLIB atoms corresponding to the encoded integer
     *  information.
     */
    public List<SMTLIBTheoryAtom> toSMTAtoms(final String varPrefix) {
        final List<SMTLIBTheoryAtom> varEqualities =
            new LinkedList<SMTLIBTheoryAtom>();
        for (final Map.Entry<AbstractVariableReference, AbstractVariableReference> e : this.refRenaming.entrySet()) {
            final AbstractVariableReference oldRef = e.getKey();
            final AbstractVariableReference newRef = e.getValue();
            if (oldRef.pointsToAnyIntegerType() && newRef.pointsToAnyIntegerType()) {
                varEqualities.add(SMTLIBIntEquals.create(oldRef.toSMTIntValue(varPrefix),
                    newRef.toSMTIntValue(varPrefix)));
            }
        }
        return varEqualities;
    }
}
