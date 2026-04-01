package aprove.input.Programs.loat;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This class represents an ITS that can directly be exported in the koat format.
 *
 * @author Constantin Mensendiek
 */
public class KoatProblem extends DefaultBasicObligation implements VariableRenaming, IRSLike {

    ImmutableSet<IGeneralizedRule> rules;
    TRSFunctionApplication start;
    CollectionMap<String, String> variableRenaming;


    public KoatProblem(ImmutableSet<IGeneralizedRule> rules,
                       TRSFunctionApplication start,
                       CollectionMap<String, String> renaming,
                       IRSProblem parent) {
        super("Koat Problem", "IntTRS in koat format");
        this.rules = rules;
        this.start = start;
        this.setVariableRenaming(renaming);
        this.setParent(parent);
    }

    public KoatProblem(ImmutableSet<IGeneralizedRule> rules,
                       TRSFunctionApplication start,
                       IRSProblem parent) {
        this(rules, start, null, parent);
        this.setVariableRenamingToIdentity();
    }

    private void setVariableRenamingToIdentity() {
        this.variableRenaming = new CollectionMap<>();
        Set<TRSVariable> allVars = new HashSet<>();
        for (IGeneralizedRule rule : rules) {
            allVars.addAll(rule.getAllVariables());
        }
        for(TRSVariable var : allVars) {
            this.variableRenaming.add(var.getName(), Collections.singleton(var.getName()));
        }
    }

    @Override
    public String getStrategyName() {
        // no strategy associated
        return null;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder sb = new StringBuilder();

        Set<TRSVariable> allVars = new HashSet<>();
        int max_number_vars = 0;
        for (IGeneralizedRule rule : this.getRules()) {
            allVars.addAll(rule.getAllVariables());
            max_number_vars = Math.max(max_number_vars, rule.getLeft().getArguments().size());

            TRSTerm r = rule.getRight();
            if(r instanceof TRSFunctionApplication) {
                max_number_vars = Math.max(max_number_vars, ((TRSFunctionApplication) r).getArguments().size());
            }
        }


        allVars = new HashSet<>();
        Set<IGeneralizedRule> rules = new HashSet<>();
        FreshNameGenerator fng = new FreshNameGenerator(allVars, FreshNameGenerator.VARIABLES);
        for (IGeneralizedRule rule : this.getRules()) {
            IGeneralizedRule new_rule = rule.fillUpVars(fng,max_number_vars);
            rules.add(new_rule);
            allVars.addAll(new_rule.getAllVariables());
        }

        String varsString = "";
        sb.append("(GOAL COMPLEXITY)\n");
        sb.append("(STARTTERM (FUNCTIONSYMBOLS " + this.getStartTerm().toString() + "))");
        sb.append(eu.linebreak());

        sb.append("(VAR");
        for (TRSVariable x : allVars) {
            if (varsString.isEmpty()) {
                varsString = "";
            } else {
                varsString += ",";
            }
            varsString += x.getName();
            sb.append(" ");
            sb.append(x.getName());
        }
        sb.append(")").append(eu.linebreak());

        sb.append("(RULES").append(eu.linebreak());

        for (IGeneralizedRule rule : rules) {
            sb.append("  " + rule.toString());
            sb.append(eu.linebreak());
        }
        sb.append(")").append(eu.linebreak());

        String complete = sb.toString();

        complete = complete.replace(":", "").replace("~", "").replace("|", ":|:").replace("FALSE", "0 = 1").replace("TRUE", "0 = 0");

        return complete;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public Set<IGeneralizedRule> getRules() {
        return rules;
    }

    @Override
    public TRSFunctionApplication getStartTerm() {
        return start;
    }

    @Override
    public IRSLike create(Set<IGeneralizedRule> rules, TRSFunctionApplication startTerm) {
        return new KoatProblem(ImmutableCreator.create(rules), startTerm, null);
    }

    @Override
    public boolean isBounded() {
        return true;
    }

    @Override
    public CollectionMap<String, String> getVariableRenaming() {
        return this.variableRenaming;
    }

    @Override
    public void setVariableRenaming(CollectionMap<String, String> variableRenaming) {
        this.variableRenaming = variableRenaming;
    }
}
