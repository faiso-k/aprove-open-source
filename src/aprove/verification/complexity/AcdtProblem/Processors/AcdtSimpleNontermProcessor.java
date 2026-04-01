package aprove.verification.complexity.AcdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.AcdtProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A really simple non-termination processor:
 *
 * If the LHS contains no defined symbols and the RHS has a subterm matched by
 * the the LHS, then the problem is nonterminating: Either the same rule can be
 * applied again or one of the arguments of the subterms is already nonterminating.
 */
public class AcdtSimpleNontermProcessor extends AcdtProblemProcessor {

    @Override
    protected boolean isCdtApplicable(AcdtProblem obl) {
        return true;
    }

    @Override
    protected Result processCdt(AcdtProblem cdtProblem, Abortion aborter)
            throws AbortionException {
        Pair<Acdt, TRSFunctionApplication> res = this.findTrivialCycle(cdtProblem);

        if (res == null) {
            return ResultFactory.unsuccessful("No trivial cycle found");
        } else {
            return ResultFactory.provedWithValue(ComplexityYNM.INFINITE, new CdtSimpleNontermProof(res.x, res.y));
        }
    }

    private Pair<Acdt, TRSFunctionApplication> findTrivialCycle(AcdtProblem cdtProblem) {
        ImmutableSet<FunctionSymbol> definedRSyms = cdtProblem.getDefinedRSymbols();
        for (Acdt cdt : cdtProblem.getTuples()) {
            TRSFunctionApplication lhs = cdt.getRuleLHS();
            if (!Collections.disjoint(
                    definedRSyms, lhs.getNonRootFunctionSymbols())) {
                continue;
            }
            for (TRSFunctionApplication arg : cdt.getRuleRHSArgs()) {
                if(lhs.matches(arg)) {
                    return new Pair<Acdt,TRSFunctionApplication>(cdt, arg);
                }
            }
        }
        return null;
    }

    private static class CdtSimpleNontermProof extends Proof.DefaultProof {

        private final Acdt cdt;
        private final TRSFunctionApplication matchingRhs;

        public CdtSimpleNontermProof(Acdt cdt, TRSFunctionApplication matchingRhs) {
            this.cdt = cdt;
            this.matchingRhs = matchingRhs;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append(o.escape("The subterm "));
            sb.append(o.export(this.matchingRhs));
            sb.append(o.escape(" of the tuple "));
            sb.append(o.export(this.cdt));
            sb.append(o.escape(" matches the left hand side, leading to non-termination"));
            return sb.toString();
        }

    }
}
