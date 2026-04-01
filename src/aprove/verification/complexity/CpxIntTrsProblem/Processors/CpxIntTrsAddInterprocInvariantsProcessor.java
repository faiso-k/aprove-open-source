package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IntTRS.InvariantGen.*;
import aprove.verification.oldframework.IntTRS.InvariantGen.AddInterprocInvariantsProcessor.*;

public class CpxIntTrsAddInterprocInvariantsProcessor extends CpxIntTrsProcessor {
    @Override
    public Result processCpxIntTrs(
        final CpxIntTrsProblem obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        //Prepare the problem, to make it look like a standard intTRS:
        final Set<CpxIntTupleRule> comRules = obl.getK().keySet();
        final Set<IGeneralizedRule> rules = new LinkedHashSet<>();
        for (final CpxIntTupleRule r : comRules) {
            rules.addAll(r.getAsSeveralRules());
        }
        final Set<FunctionSymbol> startSyms = obl.getG();

        //Get the invariants:
        final Map<FunctionSymbol, TRSFunctionApplication> invariantMap =
            AddInterprocInvariantsProcessor.callInterproc(rules, startSyms, aborter);

        //Build a new problem:
        final Map<CpxIntTupleRule, Set<CpxIntTupleRule>> ruleReplacements = new LinkedHashMap<>();
        for (final CpxIntTupleRule r : comRules) {
            final TRSFunctionApplication lhs = r.getLeft();
            final FunctionSymbol definedSym = lhs.getRootSymbol();
            if (invariantMap.containsKey(definedSym)) {
                final TRSFunctionApplication inv = invariantMap.get(definedSym);
                try {
                    ruleReplacements.put(
                        r,
                        CpxIntTupleRule.createRules(IGeneralizedRule.create(
                            lhs,
                            r.getRight(),
                            IDPv2ToIDPv1Utilities.getConjunction(r.getConstraintTerm(), inv))));

                } catch (final NoValidCpxIntTupleRuleException e) {
                    //Nothing to replace, go along.
                }
            }
        }

        return ResultFactory.proved(
            obl.replaceRules(ruleReplacements),
            UpperBound.create(),
            new CpxIntTrsAddInterprocInvariantsProof(invariantMap));
    }

    @Override
    boolean isCpxIntTrsApplicable(final CpxIntTrsProblem obl) {
        return true;
    }

    /**
     * Super-duper proof.
     * @author Marc Brockschmidt
     */
    private static class CpxIntTrsAddInterprocInvariantsProof extends AddInterprocInvariantsProof {
        public CpxIntTrsAddInterprocInvariantsProof(final Map<FunctionSymbol, TRSFunctionApplication> fsToInvariants) {
            super(fsToInvariants);
            this.setShortName("CpxIntTrsAddInterprocInvariantsProof");
            this.setLongName("AddInvariantsProof");
        }
    }
}
