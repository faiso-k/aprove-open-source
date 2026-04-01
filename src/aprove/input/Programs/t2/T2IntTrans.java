package aprove.input.Programs.t2;

import java.util.*;

import aprove.Globals;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Representation of transitions in T2-style integer transition systems.
 * @author Marc Brockschmidt
 */
public class T2IntTrans implements Exportable {
    /** The source of this transition. */
    private final int fromState;
    /** The target of this transition. */
    private final int toState;
    /** The statements for this transition. */
    private final List<T2IntTransBodyStatement> statements;

    /**
     * Creates a new integer transition
     * @param from the source state
     * @param to the target state
     * @param statements the statements happening on this transition
     */
    public T2IntTrans(final int from, final int to, final List<T2IntTransBodyStatement> statements) {
        this.fromState = from;
        this.toState = to;
        this.statements = statements;
    }

    /**
     * @param t some term
     * @param freshNames a fresh name generator
     * @return a copy of <code>t</code> where all occurrences of the constant "nondet" have been replaced by a fresh
     *  variable.
     */
    private static TRSTerm replaceNondetInTerm(final TRSTerm t, final FreshNameGenerator freshNames) {
        //Base cases:
        if (t instanceof TRSVariable) {
            return t;
        }
        final TRSFunctionApplication fa = (TRSFunctionApplication) t;
        final FunctionSymbol fs = fa.getRootSymbol();
        if ("nondet".equals(fs.getName())) {
            return TRSTerm.createVariable(freshNames.getFreshName("$nondet", false));
        }
        //Replace nondet in arguments:
        final ImmutableList<TRSTerm> oldArgs = fa.getArguments();
        final ArrayList<TRSTerm> newArgs = new ArrayList<>(oldArgs.size());
        for (final TRSTerm arg : oldArgs) {
            newArgs.add(T2IntTrans.replaceNondetInTerm(arg, freshNames));
        }
        return TRSTerm.createFunctionApplication(fs, newArgs);
    }

    /**
     * @return the source of this transition
     */
    public int getFromState() {
        return this.fromState;
    }

    /**
     * @return the target of this transition
     */
    public int getToState() {
        return this.toState;
    }

    /**
     * @return The statements in this transition
     */
    public List<T2IntTransBodyStatement> getStatements() {
        return statements;
    }

    /**
     * @return pair of the guard for this transition and the variable updates (in ssa form).
     */
    public Pair<TRSTerm, Map<TRSVariable, TRSTerm>> getGuardAndVarUpdate() {
        Map<TRSVariable, TRSTerm> varUpdate = new LinkedHashMap<>();
        TRSTerm guardTerm = null;
        final FreshNameGenerator freshNames = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        final Set<TRSVariable> allUsedVars = new LinkedHashSet<>();
        for (final T2IntTransBodyStatement statement : this.statements) {
            allUsedVars.addAll(statement.getVariables());
        }
        freshNames.lockHasNames(allUsedVars);

        for (final T2IntTransBodyStatement statement : this.statements) {
            if (statement instanceof T2IntTransRandAssignment) {
                final T2IntTransAssignment randAssign = (T2IntTransAssignment) statement;
                
                TRSVariable newVar = TRSTerm.createVariable(freshNames.getFreshName("$nondet", false));
                final LinkedHashMap<TRSVariable, TRSTerm> newUpdate = new LinkedHashMap<>(varUpdate);
                newUpdate.put(
                    randAssign.getVariable(),
                    newVar.applySubstitution(
                        TRSSubstitution.create(ImmutableCreator.create(varUpdate))));
                varUpdate = newUpdate;
            } else if (statement instanceof T2IntTransAssignment) {
                final T2IntTransAssignment assign = (T2IntTransAssignment) statement;

                final TRSVariable left = assign.getVariable();
                final TRSTerm right = assign.getValue();

                final LinkedHashMap<TRSVariable, TRSTerm> newUpdate = new LinkedHashMap<>(varUpdate);
                newUpdate.put(
                    left,
                    T2IntTrans.replaceNondetInTerm(right, freshNames).applySubstitution(
                        TRSSubstitution.create(ImmutableCreator.create(varUpdate))));
                varUpdate = newUpdate;
            } else {
                final T2IntTransGuard assumption = (T2IntTransGuard) statement;

                guardTerm =
                    IDPv2ToIDPv1Utilities.getConjunction(
                        guardTerm,
                        T2IntTrans.replaceNondetInTerm(assumption.getGuard(), freshNames).applySubstitution(
                            TRSSubstitution.create(ImmutableCreator.create(varUpdate))));
            }
        }

        return new Pair<>(guardTerm, varUpdate);
    }

    /**
     * Creates a new by adding a guard statement to this transition right in front
     * of the beforeStatement
     * @param guard The guard to prepend to this transition
     * @param beforeStatement The statement before which the guard shall be added
     * @return A new transition that has the guard statement added before <code>beforeStatement</code>
     */
    public T2IntTrans addingGuard(T2IntTransGuard guard, T2IntTransBodyStatement beforeStatement) {
        if (Globals.useAssertions) {
            assert this.statements.contains(beforeStatement);
        }
        List<T2IntTransBodyStatement> statements = new ArrayList<>(this.statements);
        statements.add(statements.indexOf(beforeStatement), guard);
        return new T2IntTrans(fromState, toState, statements);
    }
    
    /**
     * Creates a new transition by replacing one statement with another statement
     * @param toReplace The statement in this transition to replace
     * @param replaceWith The statement that should be used instead of the replaced
     * @return A new transition that has the given statement replaced
     */
    public T2IntTrans replacingStatement(T2IntTransBodyStatement toReplace, T2IntTransBodyStatement replaceWith) {
        List<T2IntTransBodyStatement> statements = new ArrayList<>(this.statements);
        if (Globals.useAssertions) {
            assert statements.contains(toReplace);
        }
        statements.set(statements.indexOf(toReplace), replaceWith);
        return new T2IntTrans(fromState, toState, statements);
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder sb = new StringBuilder();
        this.export(sb, o);
        return sb.toString();
    }

    /**
     * Pretty print this transition
     * @param sb some string builder
     * @param o some export helper
     */
    public void export(final StringBuilder sb, final Export_Util o) {
        sb.append("FROM: ").append(this.fromState).append(";").append(o.linebreak());
        for (final T2IntTransBodyStatement statement : this.statements) {
            statement.export(o, sb);
        }
        sb.append("TO: ").append(this.toState).append(";").append(o.linebreak());
    }
}
