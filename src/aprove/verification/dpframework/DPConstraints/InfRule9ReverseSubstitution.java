package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class InfRule9ReverseSubstitution extends InfRule {

    @Override
    public Pair<Constraint, InfProofStepInfo> applyToImplication(final Implication implication, final Abortion aborter)
        throws AbortionException
    {
        for (final Constraint c : implication.getConditions()) {
            if (c.isReducesTo()) {
                final ReducesTo reducesTo = (ReducesTo) c;
                if ((reducesTo.getCount().induction == 0) && reducesTo.getRight().isVariable()) {
                    if (reducesTo.getLeft() instanceof TRSFunctionApplication) {
                        if (this.irc.isGround(reducesTo.getLeft())) {
                            final RewritingVisitor rv = new RewritingVisitor(reducesTo.getLeft(), reducesTo.getRight());
                            final List<Constraint> cos = new ArrayList<Constraint>();
                            for (final Constraint co : implication.getConditions()) {
                                if (co == c) {
                                    final Count nCount = reducesTo.getCount().incInduction();
                                    //cos.add(ReducesTo.create(reducesTo.getLeft(), reducesTo.getRight(), nCount,reducesTo.getId()));
                                } else {
                                    cos.add(rv.applyTo(co));
                                }
                            }
                            final Constraint res =
                                Implication.create(
                                    implication.getId(),
                                    implication.getQuantor(),
                                    ConstraintSet.create(cos),
                                    rv.applyTo(implication.getConclusion()),
                                    implication.getData());
                            return new Pair<>(res, InfProofStepInfo.INF_DUMMY_PROOF);
                        }
                    }
                }
            }
        }
        return null;
    }

    @Override
    public InfRuleID getID() {
        return InfRuleID.IV;
    }

    @Override
    public String getLongName() {
        return "Rule IX: reverse Substitution";
    }

    @Override
    public String getName() {
        return "Rule IX";
    }

}
