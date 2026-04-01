package aprove.verification.oldframework.IRSwT.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class IRSwTUnreachableProcessor extends ProcessorSkeleton {

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode,
            Abortion aborter, RuntimeInformation rti) throws AbortionException {
        final IRSwTProblem prob = (IRSwTProblem) obl;
        final Set<IGeneralizedRule> returnValue = new LinkedHashSet<>();

        final Set<FunctionSymbol> visited = new HashSet<>();
        final Queue<FunctionSymbol> toVisit = new LinkedList<>();
        toVisit.add(prob.getStartTerm().getRootSymbol());
        while(!toVisit.isEmpty()) {
            final FunctionSymbol currentSymbol = toVisit.poll();
            visited.add(currentSymbol);

            for(IGeneralizedRule rule : prob.getRules()) {
                if(rule.getLeft().getRootSymbol().equals(currentSymbol)) {
                    returnValue.add(rule);
                    final TRSTerm rhs = rule.getRight();
                    if(rhs instanceof TRSFunctionApplication && !visited.contains(((TRSFunctionApplication)rhs).getRootSymbol())) {
                        toVisit.add(((TRSFunctionApplication)rhs).getRootSymbol());
                    }
                }
            }
        }

        return ResultFactory.proved(new IRSwTProblem(ImmutableCreator.create(returnValue), prob.getStartTerm()), YNMImplication.EQUIVALENT, new Proof.DefaultProof() {
            @Override
            public String export(Export_Util o, VerbosityLevel level) {
                return "Removed rules that are unrechable from the start term";
            }
        });
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof IRSwTProblem;
    }
}
