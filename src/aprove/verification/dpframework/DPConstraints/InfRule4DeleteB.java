package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * this InfRule remove old induction hypothesis
 * if the induction selection falls on a Reducesto which already result from a induction with induction id ID
 * all old induction hypothesis with this induction id ID.
 *
 * (Fix by thiemann: previously it was also removed deep in other induction hypothesis (possibly at positive positions of a formula)
 *   which is unsound. Now if a something has to be removed deep inside, then the whole condition is dropped from the toplevel implication)
 * @author swiste
 *
 */
public class InfRule4DeleteB extends InfRuleSelectCondition {

    @Override
    public InfRuleID getID() {
        return InfRuleID.IV;
    }

    @Override
    public String getLongName() {
        return "Rule IVB: Delete Conditions (remove old induction hypothesis)";
    }

    @Override
    public String getName() {
        return "Rule IVB";
    }

    @Override
    public Pair<Constraint, InfProofStepInfo> processSelection(
        final Implication implication,
        final ReducesTo reducesTo,
        final Set<Constraint> phiBase,
        final List<TRSVariable> vars,
        final Set<ReducesTo> preSel)
    {
        /*if (reducesTo.getCount()>1) {
            Set<Constraint> ncs = new LinkedHashSet<Constraint>(implication.getConditions());
            ncs.remove(reducesTo);
            return Implication.create(implication.getId(), implication.getQuantor(), ConstraintSet.flatCreate(ncs), implication.getConclusion());
        }*/
        if (reducesTo.getCount().getInduction() > 0) {
            // extra not kill
            final FunctionSymbol f = reducesTo.getLeftRootSymbol();
            if (f == null) {
                return null;
            }
            if (this.irc.isNonRecursive(f)) {
                return null;
            }
            // end extra not kill
            final Set<Constraint> ncs = new LinkedHashSet<>(implication.getConditions().size());
            boolean change = false;
            for (final Constraint c : implication.getConditions()) {
                final IdImplicationEraser iie = new IdImplicationEraser(reducesTo.getId());
                iie.applyTo(c);
                // if something was changed (has to be removed), then drop whole constraint!
                if (iie.isChange()) {
                    change = true;
                } else {
                    ncs.add(c);
                }
            }
            if (change) {
                final Implication imp =
                    Implication.create(
                        implication.getId(),
                        implication.getQuantor(),
                        ConstraintSet.create(ncs),
                        implication.getConclusion(),
                        implication.getData());
                return new Pair<Constraint, InfProofStepInfo>(imp, new InfRule4DeleteProof(imp));
            }
            return null;
        }
        return null;
    }

}
