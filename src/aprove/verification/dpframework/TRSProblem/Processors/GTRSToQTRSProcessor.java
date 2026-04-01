/*
 * Created on 13.04.2005
 */
package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

@NoParams
public class GTRSToQTRSProcessor extends Processor.ProcessorSkeleton {


    @Override
    public Result process(final BasicObligation o, final BasicObligationNode oblNode, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        final GTRSProblem gtrs = (GTRSProblem) o; // this cast will succeed (see isApplicable)
        final Set<GeneralizedRule> genRules = gtrs.getR();
        final boolean innermost = gtrs.getInnermost();

        QTermSet Q;
        if (innermost) {
            Q = new QTermSet(CollectionUtils.getLeftHandSides(genRules));
        } else {
            Q = new QTermSet(new ArrayList<TRSFunctionApplication>(0));
        }
        final Set<Rule> newRules = new LinkedHashSet<Rule>();
        final Set<GeneralizedRule> droppedRules = new LinkedHashSet<GeneralizedRule>();
        GeneralizedRule critRule = null;
        for (final GeneralizedRule rule : genRules) {
            if (rule instanceof Rule) {
                newRules.add((Rule) rule);
            } else {
                final TRSFunctionApplication lhs = rule.getLeft();
                final TRSTerm rhs = rule.getRight();
                // check whether we have an ordinary rule
                if (lhs.getVariables().containsAll(rhs.getVariables())) {
                    newRules.add(Rule.create(lhs, rhs));
                } else {
                    // okay, this maybe critical
                    if (innermost) {
                        if (Q.canBeRewrittenBelowRoot(lhs)) {
                            // we can drop this rule as it is never usable
                            droppedRules.add(rule);
                        } else {
                            critRule = rule;
                        }
                    } else {
                        critRule = rule;
                    }
                    // check whether this rule was critical
                    if (critRule != null) {
                        break;
                    }
                }
            }
        }

        if (critRule != null) {
            // okay, we have proven non-termination as this rule
            // yields an infinite reduction
            return ResultFactory.disproved(new CritRuleProof(critRule));
        } else {
            // we were able to remove all rules with free vars in rhs due to innermost
            // strategy and now have an usual TRS
            final QTRSProblem qtrs = QTRSProblem.create(ImmutableCreator.create(newRules), Q);
            return ResultFactory.proved(qtrs, YNMImplication.EQUIVALENT, new RRR_Q_Processor.RRR_Q_Proof(o, qtrs,
                ImmutableCreator.create(droppedRules)));
        }

    }

    @Override
    public boolean isApplicable(final BasicObligation o) {
        return o instanceof GTRSProblem;
    }


    private static final class CritRuleProof extends QTRSProof {

        private final GeneralizedRule rule;

        public CritRuleProof(final GeneralizedRule rule) {
            this.rule = rule;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return o.export("The rule ")+this.rule.export(o)+o.export(" contains free variables in its right-hand side. " +
                        "Hence the TRS is not-terminating.");
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            return CPFTag.TRS_NONTERMINATION_PROOF.create(doc, CPFTag.VARIABLE_CONDITION_VIOLATED.create(doc));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return !modus.isPositive();
        }


    }


}
