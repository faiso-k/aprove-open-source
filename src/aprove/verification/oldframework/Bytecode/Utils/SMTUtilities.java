package aprove.verification.oldframework.Bytecode.Utils;

import java.util.*;

import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv2.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Utility class holding methods useful for transforming (parts of) JBC graphs to SMT problems.
 *
 * @author Marc Brockschmidt
 */
public final class SMTUtilities {
    /**
     * Constructor that you should not use.
     */
    private SMTUtilities() {
        assert false : "Thou shall not instantiate me!";
    }

    /**
     * Convert a list of edges into SMT formulas.
     *
     * @param path The actual path.
     * @param interestingReferences an {@link InterestingReferences} object for the considered graph.
     * @param varLabel The label used for the variables encoding the first
     *  run of the loop.
     * @param includeStateInformation if true, information about integer bounds in the states will be encoded.
     * @return Pair of lists of SMT atoms. The first is the list of the formulae
     *  corresponding to computations. The second list are the conditions on the
     *  path.
     */
    public static Pair<List<SMTLIBTheoryAtom>, List<SMTLIBTheoryAtom>> convertPathToSMTFormulas(final List<Edge> path,
        final InterestingReferences interestingReferences,
        final String varLabel,
        final boolean includeStateInformation) {
        final List<SMTLIBTheoryAtom> pathComputations = new LinkedList<>();
        final List<SMTLIBTheoryAtom> pathConditions = new LinkedList<>();
        for (final Edge edge : path) {
            final EdgeInformation label = edge.getLabel();
            final State startState = edge.getStart().getState();
            final State endState = edge.getEnd().getState();
            final Set<AbstractVariableReference> startInterestingRefs;
            final Set<AbstractVariableReference> endInterestingRefs;
            if (interestingReferences != null) {
                startInterestingRefs = interestingReferences.getInterestingRefs(startState);
                endInterestingRefs = interestingReferences.getInterestingRefs(endState);
            } else {
                startInterestingRefs = null;
                endInterestingRefs = null;
            }

            for (final VariableInformation vi : label) {
                if (vi instanceof IntegerInformation && !(vi instanceof ConstantIntegerCreationInformation)
                    && ((IntegerInformation) vi).concernsInterestingRef(startInterestingRefs, endInterestingRefs)) {
                    try {
                        final IntegerInformation ii = (IntegerInformation) vi;
                        if (vi instanceof JBCIntegerRelation) {
                            pathConditions.add(ii.toSMTAtom(varLabel));
                        } else {
                            pathComputations.add(ii.toSMTAtom(varLabel));
                        }
                    } catch (final UnsupportedOperationException e) {
                        //Cannot be encoded to SMT!
                        continue;
                    }
                }
            }

            if (label instanceof RefinementEdge) {
                final RefinementEdge refinement = (RefinementEdge) label;
                for (final SMTLIBTheoryAtom a : refinement.toSMTAtoms(varLabel)) {
                    if (a instanceof SMTLIBIntEquals) {
                        final SMTLIBIntValue opA = ((SMTLIBIntEquals) a).getA();
                        final SMTLIBIntValue opB = ((SMTLIBIntEquals) a).getB();
                        if (opA instanceof SMTLIBIntConstant || opB instanceof SMTLIBIntConstant) {
                            pathConditions.add(a);
                        } else {
                            pathComputations.add(a);
                        }
                    }
                }
            } else if (label instanceof InstanceEdge) {
                pathComputations.addAll(SMTUtilities.instanceEdgeToSMTAtoms(edge, interestingReferences, varLabel, varLabel));
            } else if (label instanceof MethodSkipEdge) {
                final MethodSkipEdge mse = (MethodSkipEdge) label;
                for (final SMTLIBTheoryAtom a : mse.toSMTAtoms(varLabel)) {
                    if (a instanceof SMTLIBIntEquals) {
                        final SMTLIBIntValue opA = ((SMTLIBIntEquals) a).getA();
                        final SMTLIBIntValue opB = ((SMTLIBIntEquals) a).getB();
                        if (opA instanceof SMTLIBIntConstant || opB instanceof SMTLIBIntConstant) {
                            pathConditions.add(a);
                        } else {
                            pathComputations.add(a);
                        }
                    }
                }
            }

            if (includeStateInformation) {
                final Set<AbstractVariableReference> newRefs = endState.getReferences().keySet();
                newRefs.removeAll(startState.getReferences().keySet());
                for (final AbstractVariableReference newRef : newRefs) {
                    final AbstractVariable val = endState.getAbstractVariable(newRef);
                    if (val instanceof IntervalInt) {
                        pathConditions.addAll(((IntervalInt) val).convertBoundsToSMTConstraints(newRef, varLabel));
                    }
                }
            }
        }

        return new Pair<>(pathComputations, pathConditions);
    }

    /**
     * @param edge some instance edge
     * @param interestingReferences object describing what references are considered to be interesting in certain
     *  states. May be null.
     * @param varPrefixStart the prefix chosen for the variables generated
     *  for the source state
     * @param varPrefixEnd the prefix chosen for the variables generated for
     *  the target state
     * @return a list of equalities that connect the variables in the source
     *  state to the variables in the target state (non-constant integer
     *   variables at the same positions are connected by =)
     */
    public static List<SMTLIBTheoryAtom> instanceEdgeToSMTAtoms(final Edge edge,
        final InterestingReferences interestingReferences,
        final String varPrefixStart,
        final String varPrefixEnd) {
        final List<SMTLIBTheoryAtom> instEqualities = new LinkedList<>();
        assert (edge.getLabel() instanceof InstanceEdge);

        final Set<AbstractVariableReference> interestingRefs = new LinkedHashSet<>();
        if (interestingReferences != null) {
            interestingRefs.addAll(interestingReferences.getInterestingRefs(edge.getStart().getState()));
            interestingRefs.addAll(interestingReferences.getInterestingRefs(edge.getEnd().getState()));
        }

        final CollectionMap<AbstractVariableReference, AbstractVariableReference> refRenaming =
            edge.getRefRenamingStartToEnd(null);
        for (final Map.Entry<AbstractVariableReference, Collection<AbstractVariableReference>> e : refRenaming.entrySet()) {
            final AbstractVariableReference sourceRef = e.getKey();
            if (!sourceRef.pointsToAnyIntegerType()) {
                continue;
            }
            for (final AbstractVariableReference targetRef : e.getValue()) {
                if (!targetRef.pointsToAnyIntegerType()) {
                    continue;
                }
                //Don't encode constants:
                if (sourceRef.pointsToConstantInt() && targetRef.pointsToConstantInt()) {
                    continue;
                }
                //Don't encode really boring stuff:
                if (sourceRef.equals(targetRef) && varPrefixStart.equals(varPrefixEnd)) {
                    continue;
                }
                //Only encode if one of them is interesting:
                if (interestingReferences != null && !interestingRefs.contains(sourceRef)
                    && !interestingRefs.contains(targetRef)) {
                    continue;
                }
                instEqualities.add(SMTLIBIntEquals.create(sourceRef.toSMTIntValue(varPrefixStart),
                    targetRef.toSMTIntValue(varPrefixEnd)));
            }
        }

        return instEqualities;
    }

    /**
     * Walks through a state and exports all information about integer
     * references in the state to SMT atoms.
     * @param state some state
     * @param label some label that is prepended to all variable names.
     * @return list of SMT atoms corresponding to information about variables
     *  in <code>state</code>.
     */
    public static List<SMTLIBTheoryAtom> extractStateInvariants(final State state, final String label) {
        final List<SMTLIBTheoryAtom> stateInvariants = new LinkedList<>();
        for (final AbstractVariableReference ref : state.getReferences().keySet()) {
            final AbstractVariable val = state.getAbstractVariable(ref);
            if (val instanceof IntervalInt) {
                stateInvariants.addAll(((IntervalInt) val).convertBoundsToSMTConstraints(ref, label));
            }
        }

        return stateInvariants;
    }

    /**
     * @param smtAssignement some variable assignment provided by SMT
     * @param label a label marking the variables we are interested in
     * @return a map from abstract variable references to Long values.
     */
    public static Map<AbstractVariableReference, Long> extractVariableAssignment(final Map<String, String> smtAssignement,
        final String label) {
        final LinkedHashMap<AbstractVariableReference, Long> res = new LinkedHashMap<>();
        for (final Map.Entry<String, String> e : smtAssignement.entrySet()) {
            final String varName = e.getKey();
            if (varName.startsWith(label)) {
                final String refName = varName.substring(label.length());
                final AbstractVariableReference ref = new AbstractVariableReference(refName, OperandType.INTEGER);
                res.put(ref, Long.valueOf(e.getValue()));
            }
        }
        return res;
    }

    /**
     * @param oldVarLabel label in SMT variable names (to be replaced)
     * @param newVarLabel the new replacement label in SMT variable names
     * @param atoms a list of theory atoms on which the renamings are to be performed
     * @param factory a factory to generate new SMT atoms
     * @return a variant of <code>atoms</code>, where variable names with <code>oldVarLabel</code> as prefix have been
     *  replaced by names with <code>newVarLabel</code> as prefix.
     */
    public static List<SMTLIBTheoryAtom> renameVariablesInSMTAtoms(final String oldVarLabel,
        final String newVarLabel,
        final List<SMTLIBTheoryAtom> atoms,
        final FormulaFactory<SMTLIBTheoryAtom> factory) {
        final SMTLIBVarSubstConverter varSubst = new SMTLIBVarSubstByPrefixConverter(oldVarLabel, newVarLabel, factory);
        final ArrayList<SMTLIBTheoryAtom> res = new ArrayList<>(atoms.size());
        for (final SMTLIBTheoryAtom atom : atoms) {
            res.add(varSubst.convertAtom(atom));
        }
        return res;
    }

    /**
     * @param state some state (will not be touched)
     * @param refAssignment some ref assignment
     * @param onlyTopStackframe true iff only variables in the topmost
     *  stackframe should be assigned.
     * @return copy of <code>state</code> where we applied the information
     *  from the ref assignment.
     */
    public static State applyRefAssignmentToState(final State state,
        final Map<AbstractVariableReference, Long> refAssignment,
        final boolean onlyTopStackframe) {
        final State stateClone = state.clone();
        final HeapPositions heapPos = new HeapPositions(stateClone, true);
        for (final AbstractVariableReference ref : heapPos.getReferencesAndPositions().keySet()) {
            if (onlyTopStackframe) {
                final Collection<StatePosition> positions = heapPos.getPositionsForRef(ref);
                boolean isInTop = false;
                for (final StatePosition position : positions) {
                    final RootPosition rootPos = position.getRootPosition();
                    if (rootPos instanceof StackFramePosition && ((StackFramePosition) rootPos).getFrameNumber() == 0) {
                        isInTop = true;
                        break;
                    }
                }
                if (!isInTop) {
                    continue;
                }
            }
            //Do we have a value?
            final Long val = refAssignment.get(ref);
            if (val != null) {
                final AbstractVariable origVar = stateClone.getAbstractVariable(ref);
                assert (origVar instanceof AbstractInt) : "Trying to set non-int reference to integer value";
                final LiteralInt newVar = AbstractInt.create(val);
                final AbstractVariableReference newRef =
                    stateClone.createReferenceAndAdd(newVar, ref.getPrimitiveType());
                stateClone.replaceReference(ref, newRef);
            }
        }
        return stateClone;
    }

    public static Pair<YNM, Map<String, String>> solve (Formula<SMTLIBTheoryAtom> formula, SMTEngine smtEngine, Abortion masterAbortion, int timeout) {
        return solve(formula, smtEngine, masterAbortion.createChild(timeout));
    }

    public static Pair<YNM, Map<String, String>> solve (Formula<SMTLIBTheoryAtom> formula, SMTEngine smtEngine, Abortion abortion) {
        SMTLIBIsNonLinearChecker checker = new SMTLIBIsNonLinearChecker();
        formula.apply(checker);
        return solve(formula, smtEngine, checker, abortion);
    }

    public static Pair<YNM, Map<String, String>> solve (Formula<SMTLIBTheoryAtom> formula, SMTEngine smtEngine, SMTLIBIsNonLinearChecker checker, Abortion abortion) {
        try {
            return smtEngine.solve(Collections.singletonList(formula), (checker.formulaIsNonLinear()
                    ? SMTLogic.QF_NIA
                        : SMTLogic.QF_LIA), abortion);
        } catch (final WrongLogicException | AbortionException e) {
            // we do not care
            return new Pair<>(YNM.MAYBE, null);
        }
    }
}
