package aprove.verification.oldframework.IRSwT;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IRSwT.Utils.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * In order to obtain a readable problem, we like to rename the symbols.
 * Useful for debugging purposes, because otherwise the given problem are just unreadable!
 * @author Matthias Hoelzel
 *
 */
public class SymbolRenamingProcessor extends Processor.ProcessorSkeleton {
    /** Constructor! */
    public SymbolRenamingProcessor() {
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && !((IRSwTProblem) obl).isBounded();
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert obl instanceof IRSwTProblem;
        final IRSwTProblem irswt = (IRSwTProblem) obl;
        final SymbolNamesCollector snc = new SymbolNamesCollector(irswt.getRules());

        final LinkedHashSet<String> symbolNames = snc.getSymbolNames();
        final LinkedHashMap<String, String> newNames = this.getNewNames(symbolNames);
        final IRSwTProblem newIntTRS = this.renameProblem(irswt, newNames);

        return ResultFactory.proved(newIntTRS, YNMImplication.EQUIVALENT, new SymbolRenamingProof(newNames));
    }

    public class SymbolRenamingProof extends DefaultProof {
        LinkedHashMap<String, String> newNames;

        SymbolRenamingProof(final LinkedHashMap<String, String> nameReplacement) {
            this.newNames = nameReplacement;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append(eu.tttext("To obtain readability we use the following renaming:"));
            sb.append(eu.linebreak());
            for (final Entry<String, String> e : this.newNames.entrySet()) {
                sb.append(eu.tttext(e.getKey()));
                sb.append(eu.appSpace());
                sb.append(eu.rightarrow());
                sb.append(eu.appSpace());
                sb.append(eu.tttext(e.getValue()));
                sb.append(eu.linebreak());
            }
            return sb.toString();
        }
    }

    private IRSwTProblem renameProblem(final IRSwTProblem oldProb, final LinkedHashMap<String, String> newNames) {
        final LinkedHashSet<IGeneralizedRule> newRules = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : oldProb.getRules()) {
            final TRSFunctionApplication newLeft = (TRSFunctionApplication) this.renameTerm(rule.getLeft(), newNames);
            final TRSTerm newRight = this.renameTerm(rule.getRight(), newNames);
            final IGeneralizedRule newRule = IGeneralizedRule.create(newLeft, newRight, rule.getCondTerm());
            newRules.add(newRule);
        }

        return new IRSwTProblem(ImmutableCreator.create(newRules), oldProb.getStartTerm());
    }

    private TRSTerm renameTerm(final TRSTerm t, final LinkedHashMap<String, String> newNames) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol sym = func.getRootSymbol();
            if (IDPPredefinedMap.DEFAULT_MAP.isPredefined(sym)) {
                return t;
            } else {
                final String symbolName = sym.getName();
                assert newNames.containsKey(symbolName);
                final String newSymbolName = newNames.get(symbolName);
                final FunctionSymbol newSymbol = FunctionSymbol.create(newSymbolName, sym.getArity());
                final ArrayList<TRSTerm> newArgs = new ArrayList<>(sym.getArity());
                for (final TRSTerm arg : func.getArguments()) {
                    newArgs.add(this.renameTerm(arg, newNames));
                }
                return TRSTerm.createFunctionApplication(newSymbol, newArgs);
            }

        } else {
            return t;
        }
    }

    private LinkedHashMap<String, String> getNewNames(final LinkedHashSet<String> oldNames) {
        final LinkedHashMap<String, String> newNames = new LinkedHashMap<>(oldNames.size());
        if (oldNames.size() <= 26) {
            char currentName = 'a';
            for (final String s : oldNames) {
                newNames.put(s, "" + currentName);
                currentName += 1;
            }
        } else {
            final FreshNameGenerator fng = new FreshNameGenerator(null);
            for (final String s : oldNames) {
                newNames.put(s, fng.getFreshName("f", false));
            }
        }
        return newNames;
    }
}
