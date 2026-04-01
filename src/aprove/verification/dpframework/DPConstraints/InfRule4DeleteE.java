package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This InfRule removes ReducesTos to which too much inductions are applied
 * if the induction selection falls on a Reducesto with depth counter Depth and counter Count
 * then all ReducesTo with a depth greater than Depth+2 are removed
 * if there are also ReducesTo with the same counter Count and only one
 * of these is tail-recursive the others which are non tail-recursive are removed
 * @author swiste
 */
public class InfRule4DeleteE extends InfRuleSelectCondition {

    @Override
    public InfRuleID getID() {
        return InfRuleID.IV;
    }

    @Override
    public String getLongName() {
        return "Rule IVE: Delete Conditions (before Induction)";
    }

    @Override
    public String getName() {
        return "Rule IVE";
    }

    @Override
    public Pair<Constraint, InfProofStepInfo> processSelection(
        final Implication implication,
        final ReducesTo reducesTo,
        final Set<Constraint> phiBase,
        final List<TRSVariable> vars,
        final Set<ReducesTo> preSel)
    {
        final Count count = reducesTo.getCount();
        if (count.induction >= this.irc.getInductionCount()) {
            return null;
        }
        boolean change = false;
        final int curDepth = count.getDepth() + 2;
        final Set<Constraint> cs = new LinkedHashSet<Constraint>(implication.getConditions());
        final Iterator<Constraint> itc = cs.iterator();
        while (itc.hasNext()) {
            final Constraint c = itc.next();
            if (c.isReducesTo()) {
                final ReducesTo cRed = (ReducesTo) c;
                if (cRed.getCount().getDepth() >= curDepth) {
                    if (!this.irc.isGround(cRed.getLeft())) {
                        itc.remove();
                        change = true;
                    }
                }
            }
        }

        if (preSel != null) { // kill all but the tail-recursive ReducesTo
            // if there are more with the same counter
            final Set<ReducesTo> tailSelection = new LinkedHashSet<ReducesTo>();
            final Iterator<ReducesTo> itp = preSel.iterator();
            while (itp.hasNext()) {
                final ReducesTo crt = itp.next();
                if (crt.getCount().equals(count)) {
                    if (this.irc.isTailRecursive(crt.getLeftRootSymbol())) {
                        tailSelection.add(crt);
                    }
                } else {
                    itp.remove();
                }
            }
            if (tailSelection.size() == 1) {
                preSel.removeAll(tailSelection);
                change = cs.removeAll(preSel) || change;
            }
        }
        if (change) {
            final Implication imp =
                Implication.create(
                    implication.getQuantor(),
                    ConstraintSet.flatCreate(cs),
                    implication.getConclusion(),
                    implication.getData());
            final InfProofStepInfo info = new InfRule4DeleteProof(imp);
            return new Pair<Constraint, InfProofStepInfo>(imp, info);
        }
        return null;
    }

}
