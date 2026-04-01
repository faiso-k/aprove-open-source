package aprove.verification.oldframework.WeightedIntTrs;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Processors.ToComplexity.*;

/**
 * Just a set of rules and a start symbol. No normalization of variable names etc...
 */
public class WeightedIntTrs extends AbstractWeightedIntTermSystem<WeightedRule> implements DOT_Able {
    private ConsideredPaths consideredPaths;

    public WeightedIntTrs(Set<WeightedRule> rules, TRSFunctionApplication startTerm, String name, ConsideredPaths consideredPaths) {
        super("WeightedIntTrs", "WeightedIntTrs", name, rules, startTerm);
        this.consideredPaths = consideredPaths;
    }

    @Override
    public WeightedIntTrs copyWithNewRules (Collection<WeightedRule> newRules) {
        return new WeightedIntTrs(new LinkedHashSet<>(newRules), this.startTerm, this.name, this.consideredPaths);
    }

    @Override
    public AbstractWeightedIntTermSystem<WeightedRule> copyWithNewRules(Collection<WeightedRule> newRules, TRSFunctionApplication newStartTerm) {
        return new WeightedIntTrs(new LinkedHashSet<>(newRules), newStartTerm, this.name, this.consideredPaths);
    }

    @Override
    public String getStrategyName() {
        return "weightedIntTrs";
    }

    @Override
    public String export(Export_Util eu) {
        String res = eu.escape("IntTrs with " + rules.size() + " rules");
        res += eu.newline();
        res += eu.escape("Start term: ");
        res += startTerm.export(eu);
        res += eu.newline();
        res += eu.escape("Considered paths: ");
        res += consideredPaths.export(eu);
        res += eu.newline();
        res += eu.escape("Rules:");
        res += eu.newline();
        for (WeightedRule e: rules) {
            res += e.export(eu) + eu.newline();
        }
        return res;
    }

    @Override
    public String toString() {
        return export(new PLAIN_Util());
    }

    @Override
    public String toDOT() {
        //compute Variable renaming
        Map<TRSVariable, TRSVariable> varRenaming = new HashMap<>();
        int oC=1, iC=1, aC=1;
        for (TRSVariable var : getVariables()) {
            String newName;
            String oldName = var.getName();
            switch(oldName.charAt(0)) {
            case 'o':
                if (Character.isDigit(oldName.charAt(1)))
                    newName="o" + oC++;
                else
                    newName=oldName;
                break;
            case 'i':
                if (Character.isDigit(oldName.charAt(1)))
                    newName="i" + iC++;
                else
                    newName=oldName;
                break;
            case 'a':
                if (Character.isDigit(oldName.charAt(1)))
                    newName="a" + aC++;
                else
                    newName=oldName;
                break;
            default:
                newName=oldName;
            }
            varRenaming.put(var, TRSTerm.createVariable(newName));
        }

        //build dot String
        StringBuilder sb = new StringBuilder();
        Map<FunctionSymbol, Integer> nodeMap = new HashMap<>();
        int nodeCounter=1;

        //header copied from TerminationGraph.toDot
        sb.append("digraph dp_graph {\n"
            + "graph [mindist=0.3,nodesep=0.05,concentrate=true,ranksep=0.05];\n"
            + "node [shape=rectangle,fontsize=10,fontname=\""
            + JBCOptions.DOTTY_FONT
            + "\"];\n"
            + "edge [labeldistance=3,headclip=true,fontsize=8,fontname=\""
            + JBCOptions.DOTTY_FONT
            + "\"];\n");

        //transform each rule
        for (WeightedRule rule : getRules()) {
            //create new nodes for start and end if necessary
            FunctionSymbol l = rule.getLeft().getRootSymbol();
            if (!nodeMap.containsKey(l)) {
                sb.append(nodeCounter + " [label=\"" + l + "\"];\n");
                nodeMap.put(l, nodeCounter++);
            }
            int rightNumber;
            FunctionSymbol r = rule.getR().getRootSymbol();
            if (!nodeMap.containsKey(r)) {
                sb.append(nodeCounter + " [label=\"" + r + "\"];\n");
                nodeMap.put(r, nodeCounter++);
            }
            rightNumber = nodeMap.get(r);

            //create an edge for the rule:
            String s = rule.getWithRenamedVariables(varRenaming).toString();
            //some readability improvements
            s = s.replace(" 1 * ", " ");
            s = s.replace("(1 * ", "(");
            s = s.replace("&&", "&");
            s = s.replace(">=", "\u2265");
            s = s.replace("<=", "\u2264");

            //split into multiple lines
            sb.append(nodeMap.get(l) + " -> " + rightNumber + " [label=\"")
                .append(s.substring(0, s.indexOf("}> ")+2)).append('\n')
                .append(s.substring(s.indexOf("}> ")+3, s.indexOf(" :|: ")+4)).append('\n')
                .append(s.substring(s.indexOf(" :|: ")+5))
                .append("\"];\n");
        }
        return sb.append('}').toString();
    }

    public ConsideredPaths consideredPaths() {
        return consideredPaths;
    }

}
