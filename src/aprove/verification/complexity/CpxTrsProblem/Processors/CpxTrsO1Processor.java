package aprove.verification.complexity.CpxTrsProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Tries to prove constant runtime complexity by proving that
 * there is only a finite number of (relevant) basic terms.
 */
public class CpxTrsO1Processor extends RuntimeComplexityTrsProcessor {

    @Override
    public boolean isRuntimeComplexityTrsApplicable(final RuntimeComplexityTrsProblem obl) {
        return true;
    }

    @Override
    protected Result processRuntimeComplexityTrs(final RuntimeComplexityTrsProblem cpx, final Abortion aborter) throws AbortionException {
        final ImmutableSet<Rule> rules = cpx.getR();
        final Set<FunctionSymbol> definedSymbols = cpx.getDefinedSymbols();

        /* There are finite many (relevant) basic terms if all constructor
         * symbols occurring on the left hand side are constants.
         */
        final Set<FunctionSymbol> lhsSyms = new LinkedHashSet<FunctionSymbol>();
        for (final Rule r : rules) {
            lhsSyms.addAll(r.getLeft().getFunctionSymbols());
        }
        lhsSyms.removeAll(definedSymbols);

        for (final FunctionSymbol fs : lhsSyms) {
            if (fs.getArity() > 0) {
                return ResultFactory.unsuccessful("Found non-constant constructor symbol on the LHS of a rule");
            }
        }

        /* If the problem is terminating, it has Runtime Complexity O(1) */
        QTRSProblem terminationQtrs =
            QTRSProblem.create(ImmutableCreator.create(rules));
        if (cpx.getRewriteStrategy() != RewriteStrategy.FULL) {
            terminationQtrs = terminationQtrs.createInnermost();
        }

        return ResultFactory.proved(
                terminationQtrs,
                ComplexityIfTerminatingImplication.create(ComplexityYNM.createUpper(ComplexityValue.constant())),
                new CpxTrsO1Proof(lhsSyms));
    }

    public class CpxTrsO1Proof extends CpxProof {

        private final Collection<FunctionSymbol> relevantConstructors;

        public CpxTrsO1Proof(final Collection<FunctionSymbol> relevantConstructors) {
            this.relevantConstructors = relevantConstructors;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append(o.escape(
                    "The following constructor symbols occur on the left hand side of rules:"));
            sb.append(o.newline());
            sb.append(o.set(this.relevantConstructors, Export_Util.SIMPLESET));
            sb.append(o.newline());
            sb.append(o.escape(
                    "All of those symbols have arity 0, therefore the runtime " +
                    "complexity of this system is O(1) if the simplified " +
                    "system is terminating"));
            return sb.toString();
        }

    }

}
