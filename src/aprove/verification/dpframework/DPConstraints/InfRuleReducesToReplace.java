package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * this abstract InfRule checks each ReducesTo of the given implication
 * and asks the abstract method actionForReducesTo how to handle it,
 * if handling mode is Mode.Expand the abstract method expandTo is called.
 * for handling mode Mode.Erase the whole implication is erased.
 * expandTo can return a substitution which is applied afterwards to the new implication.
 * @author swiste
 *
 */
public abstract class InfRuleReducesToReplace extends InfRule {
    public static enum Mode {
        Expand, Erase, NoChange, Delete, ExpandDefined
    }

    @Override
    public Pair<Constraint, InfProofStepInfo> applyToImplication(final Implication implication, final Abortion aborter)
        throws AbortionException
    {
        TRSSubstitution subs = null;
        boolean change = false;
        final Set<Constraint> ncs = new LinkedHashSet<>();
        Constraint selected = null;
        Mode mode = null;
        Map<Integer, TRSVariable> newVars = null;
        for (final Constraint c : implication.getConditions()) {
            if (!change && c.isReducesTo()) {
                final ReducesTo reducesTo = (ReducesTo) c;
                mode = this.actionForReducesTo(reducesTo, implication, aborter);
                switch (mode) {
                case ExpandDefined:
                case Expand:
                case Delete:
                    change = true;
                    newVars = new LinkedHashMap<>();
                    subs = this.expandReducesTo(reducesTo, ncs, newVars, implication, aborter);
                    selected = c;
                    break;
                case Erase:
                    return new Pair<Constraint, InfProofStepInfo>(
                        ConstraintSet.emptySet,
                        new InfRule1DifferentConstructorProof(reducesTo));
                default:
                    ncs.add(c);
                }
            } else {
                ncs.add(c);
            }
        }
        if (!change || (implication.getConditions().equals(ncs))) {
            return null;
        } else {
            final ConstraintSet conditions = ConstraintSet.flatCreate(ncs);
            final Constraint conclusion = implication.getConclusion();
            if (subs != null && this.irc.isIdpMode()) {
                /*
                Set<Variable>conclusionVars = conclusion.getVariables();
                for (Map.Entry<Variable, ? extends Term> entry : subs.getMap().entrySet()) {
                    if (conclusionVars.contains(entry.getKey()) && ((IDPGInterpretation) irc.getPolyInterpretation()).isContextSensitive(entry.getValue())) {
                        return null;
                    }
                }*/
                final Map<TRSVariable, TRSTerm> sub = new LinkedHashMap<>(subs.toMap());
                final Iterator<Map.Entry<TRSVariable, TRSTerm>> subIter = sub.entrySet().iterator();
                while (subIter.hasNext()) {
                    final Map.Entry<TRSVariable, TRSTerm> entry = subIter.next();
                    if (((IDPGInterpretation) this.irc.getPolyInterpretation()).isContextSensitive(entry.getValue())) {
                        subIter.remove();
                    }
                }
                if (sub.size() == 0) {
                    return null;
                } else {
                    subs = TRSSubstitution.create(ImmutableCreator.create(sub));
                }
            }
            final Implication newImplication =
                Implication.create(implication.getQuantor(), conditions, conclusion, implication.getData());
            final Constraint res =
                (subs != null)
                    ? (Constraint) newImplication.applySubstitution(subs, this.irc.isIdpMode())
                        : newImplication;
            final InfProofStepInfo info;
            if (mode == Mode.ExpandDefined) {
                info = new InfRule7DefinedVarProof(implication, (ReducesTo) selected, newVars, (Implication) res);
            } else if (mode == Mode.Delete) {
                info = new InfRule4DeleteProof((Implication) res);
            } else if (subs == null) {
                info = new InfRule2SameConstructorProof(selected, (Implication) res);
            } else {
                final Map<TRSVariable, ? extends TRSTerm> entries = subs.toMap();
                final int n = entries.size();
                if (n == 0) {
                    // substitution is x = x
                    info = new InfRule4DeleteProof((Implication) res);
                } else {
                    assert (n <= 1); // subst is x / t
                    final Map.Entry<TRSVariable, ? extends TRSTerm> entry = subs.toMap().entrySet().iterator().next();
                    final TRSVariable x = entry.getKey();
                    final TRSTerm t = entry.getValue();
                    info = new InfRule3VariableEquationProof(x, t, (Implication) res);
                }
            }

            return new Pair<>(res, info);
        }
    }

    /**
     *
     * @param x
     * @param implication
     * @return true iff the variable x occurs in the implication in a ReducesTo in left-hand side as an argument of a defined functionsymbol
     */
    public boolean checkLeftOccur(final TRSVariable x, final Implication implication) {
        for (final Constraint con : implication.getConditions()) {
            if (con.isReducesTo()) {
                final ReducesTo reducesTo = (ReducesTo) con;
                if (reducesTo.getLeft().getVariables().contains(x)) {
                    for (final TRSTerm t : reducesTo.getLeft().getSubTerms()) {
                        if (!t.isVariable()) {
                            final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                            if (this.irc.isDefinedSymbol(fa.getRootSymbol())) {
                                if (fa.getVariables().contains(x)) {
                                    // System.out.println(this.getClass().getSimpleName()+" LeftOccur of "+x+" in "+implication);
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    public abstract TRSSubstitution expandReducesTo(
        ReducesTo reducesTo,
        Set<Constraint> ncs,
        Map<Integer, TRSVariable> newVars,
        Implication implication,
        Abortion aborter) throws AbortionException;

    public abstract Mode actionForReducesTo(ReducesTo reducesTo, Implication implication, Abortion aborter)
        throws AbortionException;
}
