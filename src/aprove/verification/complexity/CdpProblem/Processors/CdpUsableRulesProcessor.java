package aprove.verification.complexity.CdpProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdpProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Removes rules from R not reachable by the rules in P.
 */
public class CdpUsableRulesProcessor extends CdpProblemProcessor {

    @Override
    protected boolean isCdpApplicable(CdpProblem obl) {
        return true;
    }

    @Override
    protected Result processCdp(CdpProblem cdpProblem, Abortion aborter) {
        Set<Rule> usableRules = CdpUsableRulesProcessor.computeUsableRules(cdpProblem);
        if (usableRules.equals(cdpProblem.getR())) {
            return ResultFactory.unsuccessful("No rule could be removed");
        }
        ImmutableSet<Rule> newR = ImmutableCreator.create(usableRules);
        CdpProblem newProblem = CdpProblem.create(
                newR, cdpProblem.getP(), cdpProblem.getCompoundSymbols());
        return ResultFactory.proved(newProblem,
                BothBounds.create(), new CdpUsableRulesProof());
    }

    public static Set<Rule> computeUsableRules(CdpProblem cdpProblem) {
        Set<FunctionSymbol> usedSyms = CdpUsableRulesProcessor.usableSymbols(cdpProblem);
        Set<Rule> usableRules = new LinkedHashSet<Rule>();
        for (Rule r : cdpProblem.getR()) {
            if (usedSyms.contains(r.getRootSymbol())) {
                usableRules.add(r);
            }
        }
        return usableRules;
    }

    /**
     * Computes the set of symbols reachable directly or indirectly from
     * the Pairs.
     */
    private static Set<FunctionSymbol> usableSymbols(CdpProblem cdpProblem) {
        Set<FunctionSymbol> usedSyms = new HashSet<FunctionSymbol>();
        for (Rule pair : cdpProblem.getP()) {
            usedSyms.addAll(pair.getRight().getFunctionSymbols());
        }
        List<Rule> unusedRules = new LinkedList<Rule>(cdpProblem.getR());
        int size = Integer.MAX_VALUE;
        while(!unusedRules.isEmpty() && size > unusedRules.size()) {
            size = unusedRules.size();
            for (Iterator<Rule> it = unusedRules.listIterator(); it.hasNext();) {
                Rule r = it.next();
                if (usedSyms.contains(r.getRootSymbol())) {
                    usedSyms.addAll(r.getRight().getFunctionSymbols());
                    it.remove();
                }
            }
        }
        return usedSyms;
    }

    static class CdpUsableRulesProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            // FIXME: Implement real proof
            return o.escape("Removed rules which are not usable.");
        }

    }
}
