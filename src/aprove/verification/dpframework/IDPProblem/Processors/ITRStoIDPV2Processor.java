/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.Domain;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.IQTermSet.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

@NoParams
public class ITRStoIDPV2Processor extends ITRSProcessor {

    @Override
    public boolean isITRSApplicable(final ITRSProblem itrs) {
        return true;
    }

    @Override
    protected Result processITRSProblem(final ITRSProblem itrs, final Abortion aborter)
            throws AbortionException {
        // FIXME: minimal = true?
        final SharingPolyFactory polyFactory = new SharingPolyFactory();
        final aprove.verification.idpframework.Core.PredefinedFunctions.IDPPredefinedMap predefinedMap = this.convertPredefinedMap(itrs);

        final ItpfFactory itpfFactory = new SharingItpfFactory(polyFactory);

        final Collection<IRule> rules = this.convertRules(itpfFactory, predefinedMap, itrs);
        final IQTermSet q = this.convertQ(itpfFactory, predefinedMap, itrs,PredefinedQMode.ConstructorRewriting);

        return ResultFactory.proved(aprove.verification.idpframework.Core.TIDPProblem.create(itpfFactory, predefinedMap, rules, q, true, aborter), YNMImplication.EQUIVALENT, new ITRStoIDPProof());
    }

    private aprove.verification.idpframework.Core.PredefinedFunctions.IDPPredefinedMap convertPredefinedMap(final ITRSProblem itrs) {
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

    private IQTermSet convertQ(final ItpfFactory itpfFactory,
        final aprove.verification.idpframework.Core.PredefinedFunctions.IDPPredefinedMap predefinedMap,
        final ITRSProblem itrs, final IQTermSet.PredefinedQMode predefinedQMode) {
        final Set<IFunctionApplication<?>> newTerms = new LinkedHashSet<IFunctionApplication<?>>();

        for (final TRSFunctionApplication t : itrs.getQ().getExplicitTerms()) {
            newTerms.add((IFunctionApplication<?>) IDPPredefinedMap.toITerm(t, predefinedMap));
        }

        return new IQTermSet(newTerms, predefinedQMode, predefinedMap);
    }

    private Collection<IRule> convertRules(final ItpfFactory itpfFactory,
        final aprove.verification.idpframework.Core.PredefinedFunctions.IDPPredefinedMap predefinedMap,
        final ITRSProblem itrs) {

        final Set<IRule> newRules = new LinkedHashSet<IRule>();

        for (final GeneralizedRule rule : itrs.getR()) {
            final IFunctionApplication<?> newL = (IFunctionApplication<?>) IDPPredefinedMap.toITerm(rule.getLeft(), predefinedMap);
            final ITerm<?> newR = IDPPredefinedMap.toITerm(rule.getRight(), predefinedMap);

            newRules.add(IRuleFactory.create(newL, newR));
        }

        return newRules;
    }

    public class ITRStoIDPProof extends DefaultProof {
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Converted ITRS to IDPV2";
        }
    }


}
