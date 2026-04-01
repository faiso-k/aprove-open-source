package aprove.input.Programs.t2;

import java.util.*;

import aprove.Globals;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of Terminator2-outputted integer transition systems.
 *
 * @author Marc Brockschmidt, Alex Hoppen
 */
public class T2IntSys extends DefaultBasicObligation implements VariableRenaming {
    /** The start state of this transition system. */
    private int startState;

    /** The actual transitions. */
    private final Set<T2IntTrans> transitions = new LinkedHashSet<>();
    
    /** Whether or not this IntSys is an under-approximation of another IntSys */
    private boolean isUnderapproximation = false;

    /**
     * The variable renaming carried out when creating this problem
     */
    private final CollectionMap<String, String> variableRenaming = new CollectionMap<>();

    public T2IntSys() {
        super("T2IntSys", "T2-style integer transition system problem");
    }
    
    /**
     * Create a new T2IntSys by copying another T2IntSys
     * @param other The T2IntSys to be copied
     */
    public T2IntSys(T2IntSys other) {
        this();
        this.startState = other.startState;
        this.transitions.addAll(other.transitions);

        this.setParent(other.getParent());
        this.setVariableRenaming(other.getVariableRenaming());
    }

    /**
     * @param start the start state of this system
     */
    public void setStartState(final int start) {
        this.startState = start;
    }

    /**
     * @param trans another transition for this system.
     */
    public void addTransition(final T2IntTrans trans) {
        this.transitions.add(trans);
    }
    
    public void replaceTransition(final T2IntTrans oldTrans, final T2IntTrans newTrans) {
        this.transitions.remove(oldTrans);
        this.transitions.add(newTrans);
    }

    /**
     * @return the actual transitions. NOTE: Internal set, so modification changes the system.
     */
    public Set<T2IntTrans> getTransitions() {
        return this.transitions;
    }

    /**
     * @return the start state of this system.
     */
    public int getStartState() {
        return this.startState;
    }

    /** {@inheritDoc} */
    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    /** {@inheritDoc} */
    @Override
    public String export(final Export_Util o) {
        final StringBuilder res = new StringBuilder();
        res.append("START: ").append(this.startState).append(';').append(o.linebreak());
        res.append(o.cond_linebreak());

        for (final T2IntTrans trans : this.transitions) {
            trans.export(res, o);
            res.append(o.linebreak());
        }

        return res.toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "t2Sys";
    }
    
    public boolean isUnderapproximation() {
        return isUnderapproximation;
    }
    
    /**
     * Splits the given term into its conjunction subterms and adds all statements of the form 
     * var < term or var > term to the given set.
     * 
     * @param term The term from which all simple guard statements should be extracted
     * @param variablesWithGuard The set to which the simple guard statements should be added
     */
    private void addSimpleGuardStatementsToSet(TRSTerm term, Set<String> variablesWithGuard) {
        if (Globals.useAssertions) {
            assert variablesWithGuard != null;
        }
        if (term instanceof TRSCompoundTerm) {
            TRSCompoundTerm compoundTerm = (TRSCompoundTerm)term;
            String functionName = compoundTerm.getFunctionSymbol().getName();
            if (functionName.equals("&&")) {
                for (TRSTerm subTerm : compoundTerm.getArguments()) {
                    addSimpleGuardStatementsToSet(subTerm, variablesWithGuard);
                }
            } else if (functionName.equals("<") || functionName.equals(">")) {
                for (TRSTerm arg : compoundTerm.getArguments()) {
                    if (arg instanceof TRSVariable) {
                        TRSVariable variable = (TRSVariable)arg;
                        variablesWithGuard.add(variable.getName());
                    }
                }
            }
            
        }
    }
    
    /**
     * Iterates through all variable assignments and replaces all variables
     * in the assignment with the assigned value if the assignment has been made before
     * E.g.
     * <pre>
     * x0 := oldX0 + 1
     * x1 := x2 + x0
     * x2 := x0
     * </pre>
     * 
     * becomes
     * 
     * <pre>
     * x0 := oldX0 + 1
     * x1 := x2 + (oldX0 + 1)
     * x2 := oldX0 + 1
     * </pre>
     * @return
     */
    private T2IntSys resolvingVariables() {
        T2IntSys updatedProblem = new T2IntSys(this);
        
        for (T2IntTrans transition : getTransitions()) {
            T2IntTrans updatedTransition = transition;
            Map<TRSTerm, TRSTerm> definedVariables = new HashMap<>();
            for (T2IntTransBodyStatement statement : transition.getStatements()) {
                if (statement instanceof T2IntTransAssignment) {
                    T2IntTransAssignment assignment = (T2IntTransAssignment)statement;
                    TRSVariable variable = assignment.getVariable();
                    if (!(statement instanceof T2IntTransRandAssignment)) {
                        TRSTerm newTerm = assignment.getValue().replaceAll(definedVariables);
                        newTerm = newTerm.simplify();
                        T2IntTransAssignment newAssignment = new T2IntTransAssignment(variable, newTerm);
                        updatedTransition = updatedTransition.replacingStatement(statement, newAssignment);
                        definedVariables.put(variable, newTerm);
                    }
                    // Remove all variables that use this variable in its definition, 
                    // since the definition is now no longer valid
                    for(Iterator<Map.Entry<TRSTerm, TRSTerm>> it = definedVariables.entrySet().iterator(); it.hasNext(); ) {
                        Map.Entry<TRSTerm, TRSTerm> entry = it.next();
                        if (entry.getValue().getVariables().contains(variable)) {
                            it.remove();
                        }
                    }
                } else if (statement instanceof T2IntTransGuard) {
                    T2IntTransGuard guard = (T2IntTransGuard)statement;
                    TRSTerm newTerm = guard.getGuard().replaceAll(definedVariables);
                    T2IntTransGuard newGuard = new T2IntTransGuard(newTerm);
                    updatedTransition = updatedTransition.replacingStatement(guard, newGuard);
                }
            }
            updatedProblem.replaceTransition(transition, updatedTransition);
        }
        return updatedProblem;
    }
    
    /**
     * Replace all multiplications of the form <code>c * v</code> where <code>c <= upToConstant</code>
     * by <code>v + v + ... + v</code>
     *  
     * @param upToConstant Up to which constant should constant multiplications be unfolded?
     * @return A new term that has all constant multiplications with constants smaller than the 
     * parameter unfoled to a sum
     */
    public T2IntSys unfoldConstantMultiplication(int upToConstant) {
        T2IntSys updatedProblem = new T2IntSys(this);
        
        for (T2IntTrans transition : getTransitions()) {
            T2IntTrans updatedTransition = transition;
            
            for (T2IntTransBodyStatement statement : transition.getStatements()) {
                if (statement instanceof T2IntTransAssignment) {
                    T2IntTransAssignment assignment = (T2IntTransAssignment)statement;
                    if (!(statement instanceof T2IntTransRandAssignment)) {
                        TRSTerm newTerm = assignment.getValue().unfoldConstantMultiplication(upToConstant);
                        T2IntTransAssignment newAssignment = new T2IntTransAssignment(assignment.getVariable(), newTerm);
                        updatedTransition = updatedTransition.replacingStatement(assignment, newAssignment);
                    }
                } else if (statement instanceof T2IntTransGuard) {
                    T2IntTransGuard guard = (T2IntTransGuard)statement;
                    TRSTerm newTerm = guard.getGuard().unfoldConstantMultiplication(upToConstant);
                    T2IntTransGuard newGuard = new T2IntTransGuard(newTerm);
                    updatedTransition = updatedTransition.replacingStatement(guard, newGuard);
                }
            }
            
            updatedProblem.replaceTransition(transition, updatedTransition);
        }
        
        return updatedProblem;
    }
    
    /**
     * Transforms this IntSys into a different T2IntSys that is an under-approximation 
     * of the given system by applying the following heuristics:
     * <ul>
     *   <li> For each statement of the form x = oldX + ... add an assume(x >= 0)
     *   <li> For each statement of the form x = oldX - const add an assume(x <= 0)
     * </ul>
     * 
     * @param addedGuardStatements If non-null this list will contain all guard statements
     * that were added for each transition while under-approximating the problem
     * @return A problem that is an under-approximation of the this problem 
     */
    public T2IntSys underapproximate(Map<Integer, List<T2IntTransGuard>> addedGuardStatements) {
        T2IntSys updatedProblem = new T2IntSys(this);
        updatedProblem = updatedProblem.resolvingVariables();
        updatedProblem.isUnderapproximation = true;
        
        Set<T2IntTrans> transitions = new LinkedHashSet<>(updatedProblem.getTransitions());
        for (T2IntTrans transition : transitions) {
            T2IntTrans updatedTransition = transition;
            Set<String> variablesWithGuard = new LinkedHashSet<>();
            for (T2IntTransBodyStatement statement : transition.getStatements()) {
                if (statement instanceof T2IntTransGuard) {
                    T2IntTransGuard guard = (T2IntTransGuard)statement;
                    addSimpleGuardStatementsToSet(guard.getGuard(), variablesWithGuard);
                } else if (statement instanceof T2IntTransAssignment) {
                    T2IntTransAssignment assignment = (T2IntTransAssignment)statement;
                    TRSVariable assignedVariable = assignment.getVariable();
                    String assignedVariableName = assignedVariable.getName();
                    if (assignment.getValue() instanceof TRSCompoundTerm) {
                        TRSCompoundTerm compoundTerm = (TRSCompoundTerm)assignment.getValue();
                        FunctionSymbol fs = compoundTerm.getFunctionSymbol();
                        
                        if (variablesWithGuard.contains(assignedVariableName)) {
                            continue;
                        }
                        
                        T2IntTransGuard newGuardStatement = null;
                        
                        // Apply heuristics for plus
                        if (fs.getName().equals("+")) {
                            // Look if the old variable occurs on the right-hand-side
                            TRSVariable guardVariable = null;
                            for (TRSTerm arg : compoundTerm.getArguments()) {
                                if (arg instanceof TRSVariable) {
                                    TRSVariable variable = (TRSVariable)arg;
                                    if (variable.getName().equals(assignedVariableName)) {
                                        guardVariable = assignedVariable;
                                        break;
                                    }
                                }
                            }
                            
                            if (guardVariable != null) {
                                TRSTerm greaterZero = TRSTerm.createFunctionApplication(FunctionSymbol.create(">=", 2), assignment.getVariable(), TRSTerm.createConstant("0"));
                                newGuardStatement = new T2IntTransGuard(greaterZero);
                            }
                        } else if (fs.getName().equals("-")) {
                            // Check if the right-side is of the form oldVariable - constant
                            TRSVariable guardVariable = null;
                            FunctionSymbol functionSymbol = compoundTerm.getFunctionSymbol();
                            if (functionSymbol.getName().equals("-") && functionSymbol.getArity() == 2) {
                                if (compoundTerm.getArgument(0) instanceof TRSVariable && ((TRSVariable)compoundTerm.getArgument(0)).getName().equals(assignedVariableName)) {
                                    if (compoundTerm.getArgument(1) instanceof TRSConstantTerm) {
                                        guardVariable = assignedVariable;
                                    }
                                }
                            }
                            
                            if (guardVariable != null) {
                                TRSTerm greaterZero = TRSTerm.createFunctionApplication(FunctionSymbol.create("<=", 2), guardVariable, TRSTerm.createConstant("0"));
                                newGuardStatement = new T2IntTransGuard(greaterZero);
                            }
                        }
                        
                        // Add the guard statement
                        if (newGuardStatement != null) {
                            variablesWithGuard.add(assignedVariableName);
                            updatedTransition = updatedTransition.addingGuard(newGuardStatement, statement);
                            
                            // Add the guard statement to the log
                            if (addedGuardStatements != null) {
                                if (addedGuardStatements.get(transition.getFromState()) == null) {
                                    addedGuardStatements.put(transition.getFromState(), new ArrayList<>());
                                }
                                addedGuardStatements.get(transition.getFromState()).add(newGuardStatement);
                            }
                        }
                    }
                }
            }
            updatedProblem.replaceTransition(transition, updatedTransition);
        }
        return updatedProblem;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public CollectionMap<String, String> getVariableRenaming() {
        return variableRenaming;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void setVariableRenaming(CollectionMap<String, String> variableRenaming) {
        this.variableRenaming.putAll(variableRenaming);
    }
}
