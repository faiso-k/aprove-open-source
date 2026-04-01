package aprove.verification.complexity.WdpCProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.WdpCProblem.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class WdpUsableRulesProcessor extends WdpProblemProcessor {

    @Override
    protected boolean isWdpApplicable(WDPProblemRC obl) {
        return true;
    }

    @Override
    protected Result processWdp(WDPProblemRC wdpProblem, Abortion aborter) {
        Set<FunctionSymbol> usedSyms = this.usableSymbols(wdpProblem);
        Set<Rule> usableRules = new LinkedHashSet<Rule>();
        for (Rule r : wdpProblem.getR()) {
            if (usedSyms.contains(r.getRootSymbol())) {
                usableRules.add(r);
            }
        }
        ImmutableSet<Rule> newR = ImmutableCreator.create(usableRules);
        if (newR.equals(wdpProblem.getR())) {
            return ResultFactory.unsuccessful();
        } else {
            WDPProblemRC newProblem = WDPProblemRC.create(
                    newR, wdpProblem.getP(), wdpProblem.getCompoundSymbols(),
                    wdpProblem.getDefinedRSymbols(),
                    wdpProblem.isInnermost());
            return ResultFactory.proved(newProblem,
                    BothBounds.create(), new WdpUsableRulesProof());
        }
    }

    /**
     * Computes the set of symbols reachable directly or indirectly from
     * the Pairs.
     */
    private Set<FunctionSymbol> usableSymbols(WDPProblemRC wdpProblem) {
        Set<FunctionSymbol> usedSyms = new HashSet<FunctionSymbol>();
        for (Rule pair : wdpProblem.getP()) {
            usedSyms.addAll(pair.getRight().getFunctionSymbols());
        }
        List<Rule> unusedRules = new LinkedList<Rule>(wdpProblem.getR());
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

    static class WdpUsableRulesProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            // FIXME: Implement real proof
            return o.escape("Removed rules which are not usable.");
        }

    }
}
