package aprove.verification.dpframework.IDPProblem.Processors.itpfExecution;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public class ItpfSchedulerProof extends DefaultProof implements IDPExportable {

    protected static final Set<IItpfRule> emptyGroup = Collections.<IItpfRule>emptySet();

    protected final Map<IItpfRule, Set<IItpfRule>> ruleGrouping;
    protected final List<ImmutablePair<IItpfRule, Itpf>> steps;

    public ItpfSchedulerProof(Map<IItpfRule, Set<IItpfRule>> ruleGrouping) {
        this.steps = new ArrayList<ImmutablePair<IItpfRule, Itpf>>();
        this.ruleGrouping = ruleGrouping;
    }

    public void addStep(IItpfRule rule, Itpf result) {
        this.steps.add(new ImmutablePair<IItpfRule, Itpf>(rule, result));
    }

    public boolean isEmptyProof() {
        return this.steps.isEmpty();
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        return this.export(o, null, level);
    }

    @Override
    public String export(Export_Util o, IDPPredefinedMap predefinedMap,
            VerbosityLevel verbosityLevel) {
        StringBuilder sb = new StringBuilder();
        this.exportSteps(sb, o, predefinedMap, verbosityLevel);
        return sb.toString();
    }

    protected void exportSteps(StringBuilder sb, Export_Util o, IDPPredefinedMap predefinedMap, VerbosityLevel verbosityLevel) {
        Set<IItpfRule> currentGroup = null;
        List<IItpfRule> stepRules = new ArrayList<IItpfRule>(this.steps.size());
        ImmutablePair<IItpfRule, Itpf> lastStep = null;
        for (ImmutablePair<IItpfRule, Itpf> step : this.steps) {
            Set<IItpfRule> ruleGroup = this.ruleGrouping.get(step.x);
            if (ruleGroup == null) {
               ruleGroup = ItpfSchedulerProof.emptyGroup;
            }
            if (currentGroup == null) {
                currentGroup = ruleGroup;
            }
            if (verbosityLevel == VerbosityLevel.HIGH && lastStep != null &&
                (currentGroup == ItpfSchedulerProof.emptyGroup || (currentGroup != ruleGroup && !currentGroup.contains(step.x)))) {
                currentGroup = ruleGroup;
                this.exportStep(stepRules, lastStep.y, sb, o, predefinedMap, verbosityLevel);
                stepRules.clear();
            }
            currentGroup = ruleGroup;
            stepRules.add(step.x);
            lastStep = step;
        }
        if (!stepRules.isEmpty()) {
            this.exportStep(stepRules, lastStep.y, sb, o, predefinedMap, verbosityLevel);
        }
        sb.append(o.linebreak());
    }


    protected void exportStep(List<IItpfRule> stepRules, Itpf result, StringBuilder sb, Export_Util o, IDPPredefinedMap predefinedMap, VerbosityLevel verbosityLevel) {
        /*
        if (stepRules.size() > 1) {
            sb.append("Aplying the rules ");
        } else {
            sb.append("Applying the rule ");
        }*/
        Iterator<IItpfRule> stepRulesIter = stepRules.iterator();
        while (stepRulesIter.hasNext()) {
            IItpfRule rule = stepRulesIter.next();
            sb.append(rule.getDescription(NameLength.SHORT).export(o));
            if (stepRulesIter.hasNext()) {
                sb.append(", ");
            }
        }
        sb.append(":");
        sb.append(o.linebreak());
        sb.append("\t");
        sb.append(result.export(o, predefinedMap, verbosityLevel));
        sb.append(o.linebreak());
    }
}
