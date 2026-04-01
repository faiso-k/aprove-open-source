package aprove.verification.complexity.CpxITrsProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CIdtProblem.*;
import aprove.verification.complexity.CpxITrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.Domain;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author Marcel Klinzing
 */
public class CpxITrsToCIdtProcessor extends CpxITrsProcessor {

    @Override
    protected boolean isCpxITrsApplicable(CpxITrsProblem obl) {
        return true;
    }

    @Override
    protected Result processCpxITrs(CpxITrsProblem itrs, Abortion aborter)
            throws AbortionException {

        final SharingPolyFactory polyFactory = new SharingPolyFactory();
        final IDPPredefinedMap predefinedMap = this.convertPredefinedMap(itrs);

        final ItpfFactory itpfFactory = new SharingItpfFactory(polyFactory);

        final Collection<IRule> rules = this.convertRules(itpfFactory, predefinedMap, itrs);
        final IQTermSet q = IQTermSet.createConstructorQ(rules, predefinedMap);
        CIdtProblem cidt = CIdtProblem.create(itpfFactory, predefinedMap, rules, q, aborter);
        return ResultFactory.proved(cidt, BothBounds.create(),
            new CpxITrsToCIdtProof());
    }

    private IDPPredefinedMap convertPredefinedMap(CpxITrsProblem itrs) {
        final Map<ImmutablePair<String, Integer>, aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction<?, ?>> mapping = new LinkedHashMap<ImmutablePair<String,Integer>, aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction<?,?>>();

        for (final Map.Entry<FunctionSymbol, PredefinedFunction<? extends Domain>> mapEntry : itrs.getPredefinedMap().getMapping().entrySet()) {
            final ImmutablePair<String, Integer> nameArity = new ImmutablePair<String, Integer>(mapEntry.getKey().getName(), mapEntry.getKey().getArity());
            final aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction<?, ?> predefFunction = this.convertPredefinedFunction(mapEntry.getValue());

            mapping.put(nameArity, predefFunction);
        }

        final IDPPredefinedMap newMap = new IDPPredefinedMap(ImmutableCreator.create(mapping), IDPPredefinedMap.getUsedFunctionSymbolsFromOldTerms(itrs.getTerms()));

        return newMap;
    }

    private aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction<?, ?> convertPredefinedFunction(final PredefinedFunction<? extends Domain> function) {
        final String funcName = function.getFunc().name();
        final aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction.Func newFunc = Enum.valueOf(aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction.Func.class, funcName);

        if (function.isArithmetic() || function.isBitwise()) {
            if (function.getArity() == 1) {
                return PredefinedSemanticsFactory.createFunction(newFunc, ImmutableCreator.create(java.util.Collections.singletonList(DomainFactory.INTEGERS)));
            } else if (function.getArity() == 2) {
                return PredefinedSemanticsFactory.createFunction(newFunc, DomainFactory.INTEGER_INTEGER);
            }
        } else if (function.isRelation()) {
            return PredefinedSemanticsFactory.createFunction(newFunc, DomainFactory.INTEGER_INTEGER);
        } else if (function.isBoolean()) {
            if (function.getArity() == 1) {
                return PredefinedSemanticsFactory.createFunction(newFunc, ImmutableCreator.create(java.util.Collections.singletonList(DomainFactory.BOOLEANS)));
            } else if (function.getArity() == 2) {
                return PredefinedSemanticsFactory.createFunction(newFunc, DomainFactory.BOOLEAN_BOOLEAN);
            }
        }

        throw new UnsupportedOperationException("function can not be converted: " + function);
    }

    private Collection<IRule> convertRules(final ItpfFactory itpfFactory,
        final aprove.verification.idpframework.Core.PredefinedFunctions.IDPPredefinedMap predefinedMap,
        final CpxITrsProblem itrs) {

        final Set<IRule> newRules = new LinkedHashSet<IRule>();

        for (final GeneralizedRule rule : itrs.getR()) {
            final IFunctionApplication<?> newL = (IFunctionApplication<?>) IDPPredefinedMap.toITerm(rule.getLeft(), predefinedMap);
            final ITerm<?> newR = IDPPredefinedMap.toITerm(rule.getRight(), predefinedMap);

            newRules.add(IRuleFactory.create(newL, newR));
        }

        return newRules;
    }


    public class CpxITrsToCIdtProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Converted CpxITrs-problem To CIdt-problem";
        }

    }
}
