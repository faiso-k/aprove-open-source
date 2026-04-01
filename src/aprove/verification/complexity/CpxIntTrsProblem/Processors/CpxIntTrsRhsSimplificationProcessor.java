package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class CpxIntTrsRhsSimplificationProcessor extends CpxIntTrsProcessor {

    public static class RhsSimplificationProof extends Proof.DefaultProof {

        private Map<CpxIntTupleRule, CpxIntTupleRule> replaced;

        public RhsSimplificationProof(Map<CpxIntTupleRule, CpxIntTupleRule> replaced) {
            this.replaced = replaced;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append(o
                .escape("The following rules were simplified by removing trailing parts of their right-hand sides:"));
            sb.append(o.cond_linebreak());
            for (Entry<CpxIntTupleRule, CpxIntTupleRule> e : this.replaced.entrySet()) {
                sb.append("The rule " + o.cond_linebreak());
                sb.append(e.getKey().export(o));
                sb.append(o.cond_linebreak() + "was replaced by: " + o.cond_linebreak());
                sb.append(e.getValue().export(o));
                sb.append(o.cond_linebreak());
            }
            return sb.toString();
        }
    }

    @Override
    public Result processCpxIntTrs(
        CpxIntTrsProblem obl,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti) throws AbortionException
    {
        Map<CpxIntTupleRule, Set<CpxIntTupleRule>> replacements = new LinkedHashMap<>();
        Map<CpxIntTupleRule, CpxIntTupleRule> replacementsForProof = new LinkedHashMap<>();

        CpxIntGraph g = obl.getDepGraph(aborter);
        for (CpxIntTupleRule rule : obl.getK().keySet()) {
            Set<CpxIntTupleRule> out = g.getOut(rule);
            Set<FunctionSymbol> lhsSyms = new LinkedHashSet<>();
            for (CpxIntTupleRule outRule : out) {
                lhsSyms.add(outRule.getRootSymbol());
            }
            ImmutableList<TRSFunctionApplication> rights = rule.getRights();
            ArrayList<TRSFunctionApplication> newRights = new ArrayList<>();
            for (TRSFunctionApplication rhs : rights) {
                if (lhsSyms.contains(rhs.getRootSymbol())) {
                    newRights.add(rhs);
                }
            }
            if (newRights.size() == rights.size()) {
                continue;
            }
            TRSFunctionApplication newRhs = TRSTerm.createFunctionApplication(CpxIntTermHelper.getComSymbol(newRights.size()), newRights);
            CpxIntTupleRule newRule = rule.replaceRhs(newRhs);
            Set<CpxIntTupleRule> newRules = new LinkedHashSet<>();
            newRules.add(newRule);
            replacements.put(rule, newRules);
            replacementsForProof.put(rule, newRule);
        }

        if (replacements.isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        return ResultFactory.proved(
            obl.replaceRules(replacements),
            BothBounds.create(),
            new RhsSimplificationProof(replacementsForProof));
    }

    @Override
    boolean isCpxIntTrsApplicable(CpxIntTrsProblem obl) {
        return true;
    }

}
