package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.idp.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public abstract class InfRuleSelectCondition extends InfRule {

    @Override
    public Pair<Constraint, InfProofStepInfo> applyToImplication(final Implication implication, final Abortion aborter)
        throws AbortionException
    {
        FunctionSymbol f = null;
        List<TRSVariable> selVars = null;
        Set<ReducesTo> preSel = new LinkedHashSet<ReducesTo>();
        ReducesTo selection = null;
        TRSTerm q = null;
        final Set<Constraint> phiBase = new LinkedHashSet<Constraint>();
        Loop: for (final Constraint c : implication.getConditions()) {
            if (c.isReducesTo()) {
                List<TRSVariable> vars;
                final ReducesTo reducesTo = (ReducesTo) c;
                q = reducesTo.getRight();
                if (reducesTo.getId() != this.irc.getInductionBlockId()
                    && null != (f = reducesTo.getLeftRootSymbol())
                    // f == null => f is Vaiable => no induction rule match
                    && (!this.irc.isIdpMode() || !((IdpInductionCalculus) this.irc)
                        .getIdp()
                        .getRuleAnalysis()
                        .getPreDefinedMap()
                        .isPredefined(f))
                    // if f is predefined symbol, constant folding is better
                    && this.irc.isDefinedSymbol(f)
                    // f is not defined => no induction rule match
                    && null != (vars = this.irc.getPDVaribales((TRSFunctionApplication) reducesTo.getLeft()))
                    //  null == null => no pairwise different => no induction rule match
                    && ((this.irc.isIdpMode() && reducesTo.getParentFunc() != null && !reducesTo
                        .getParentFunc()
                        .canMatchPredefLhs(
                            reducesTo.getLeft(),
                            ((IdpInductionCalculus) this.irc).getIdp().getRuleAnalysis().getPreDefinedMap())) || !reducesTo
                        .getLeft()
                        .unifies(q))
                // unification is possible => no induction rule match
                )
                {
                    if (this.irc.isNonRecursive(f)) {
                        selection = reducesTo;
                        selVars = vars;
                        preSel = null;
                        break Loop;
                    }
                    preSel.add(reducesTo);
                    if (selection == null || selection.getCount().greaterThan(reducesTo.getCount())) {
                        selection = reducesTo;
                        selVars = vars;
                    }
                }
            }
        }
        if (selection == null) {
            return null;
        }
        for (final Constraint c : implication.getConditions()) {
            if (c != selection) {
                phiBase.add(c);
            }
        }
        return this.processSelection(implication, selection, phiBase, selVars, preSel);
    }

    public abstract Pair<Constraint, InfProofStepInfo> processSelection(
        Implication implication,
        ReducesTo reducesTo,
        Set<Constraint> phiBase,
        List<TRSVariable> vars,
        Set<ReducesTo> preSel);
}
