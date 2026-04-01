package aprove.verification.complexity.CdtProblem;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.complexity.AcdtProblem.Utils.TupleDefinedPositions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Complexity Dependency Tuple
 */
public class Cdt implements Exportable, Immutable, HasFunctionSymbols, HasLHS, HasRootSymbol, HasVariables, CPFAdditional {

    private final Rule depTuple;

    private Cdt(Rule depTuple) {
        this.depTuple = depTuple;
    }

    public static Cdt create(Rule depTuple) {
        return new Cdt(depTuple);
    }

    public static Cdt createFromRule(FreshNameGenerator fng, Rule rule,
            List<Position> definedSymbolPositions) {
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        TRSTerm ruleRhs = rule.getRight();
        for (Position p : definedSymbolPositions) {
            args.add(Cdt.makePairTerm(fng, (TRSFunctionApplication)ruleRhs.getSubterm(p)));
        }

        FunctionSymbol rootSym = rule.getRootSymbol();
        FunctionSymbol pairSym = FunctionSymbol.create(
                fng.getFreshName(rootSym.getName(), true),
                rootSym.getArity());
        TRSFunctionApplication pairLhs =
            TRSTerm.createFunctionApplication(pairSym, rule.getLeft().getArguments());
        FunctionSymbol compoundSym = FunctionSymbol.create(
                fng.getFreshName("c", false, FreshNameGenerator.APPEND_NUMBERS),
                args.size());
        TRSTerm pairRhs = TRSTerm.createFunctionApplication(compoundSym, args);
        return Cdt.create(Rule.create(pairLhs, pairRhs));
    }

    public static Cdt createFromRule(FreshNameGenerator fng, Rule rule,
            TupleDefinedPositions tdps) {
        return Cdt.createFromRule(fng, rule, tdps.getPositions());
    }

    public static Cdt createFromRule(FreshNameGenerator fng, Rule rule,
            Set<FunctionSymbol> definedSymbols) {
        TupleDefinedPositions tdps = TupleDefinedPositions.createFromRule(rule, definedSymbols);
        return Cdt.createFromRule(fng, rule, tdps);
    }

    public static List<Cdt> createForParallelFromRule(FreshNameGenerator fng, Rule rule,
            TupleDefinedPositions tdps) {
        List<Cdt> result = new ArrayList<Cdt>();
        List<List<Position>> maximalChains = tdps.getMaximalPrefixChains();
        if (maximalChains.isEmpty()) {
            // special case: no chains = no defined symbols in rhs,
            // but we still need one Cdt to represent the rule
            Cdt cdt = Cdt.createFromRule(fng, rule, Collections.emptyList());
            result.add(cdt);
        }
        else {
            for (List<Position> positionChain : maximalChains) {
                Cdt cdt = Cdt.createFromRule(fng, rule, positionChain);
                result.add(cdt);
            }
        }
        return result;
    }

    private static TRSFunctionApplication makePairTerm(FreshNameGenerator fng,
            TRSFunctionApplication fa) {
        final FunctionSymbol pairSym = FunctionSymbol.create(
                fng.getFreshName(fa.getRootSymbol().getName(), true),
                fa.getRootSymbol().getArity());
        TRSFunctionApplication pairTerm =
            TRSTerm.createFunctionApplication(pairSym, fa.getArguments());
        return pairTerm;
    }

    public Cdt filter(BitSet removeTupleparts) {
        List<TRSFunctionApplication> oldArgs = this.getRuleRHSArgs();
        List<TRSFunctionApplication> newArgs =
            new ArrayList<TRSFunctionApplication>(removeTupleparts.size());
        int oldArity = oldArgs.size();
        for (int i=0; i < oldArity; i++) {
            if (!removeTupleparts.get(i)) {
                newArgs.add(oldArgs.get(i));
            }
        }

        // FIXME: We need a new safe compound symbol here!
        FunctionSymbol newRhsFuncSym = FunctionSymbol.create(
                this.getRuleRHS().getRootSymbol().getName(),
                oldArity - removeTupleparts.cardinality());
        TRSFunctionApplication newRhs =
            TRSTerm.createFunctionApplication(newRhsFuncSym, newArgs);
        Rule newRule = Rule.create(this.getRuleLHS(), newRhs);

        return new Cdt(newRule);
    }

    public Cdt applySubstitution(TRSSubstitution sigma) {
        return new Cdt(this.depTuple.applySubstitution(sigma));
    }

    public Rule getRule() {
        return this.depTuple;
    }

    public TRSFunctionApplication getRuleLHS() {
        return this.depTuple.getLeft();
    }

    public TRSFunctionApplication getRuleRHS() {
        /* RHS of a CDT is always a function application */
        return (TRSFunctionApplication)this.depTuple.getRight();
    }

    public FunctionSymbol getCompoundSym() {
        return this.getRuleRHS().getRootSymbol();
    }

    public Set<FunctionSymbol> getPairSyms() {
        LinkedHashSet<FunctionSymbol> result =
            new LinkedHashSet<FunctionSymbol>(this.getRuleRHSArgs().size()+1);
        result.add(this.getRuleLHS().getRootSymbol());
        for (TRSFunctionApplication arg : this.getRuleRHSArgs()) {
            result.add(arg.getRootSymbol());
        }
        return result;
    }

    @SuppressWarnings({"unchecked","rawtypes"})
    public ImmutableList<TRSFunctionApplication> getRuleRHSArgs() {
        return (ImmutableList)this.getRuleRHS().getArguments();
    }

    @Override
    public String export(Export_Util eu) {
        return this.depTuple.export(eu);
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return this.depTuple.toCPF(doc, xmlMetaData);
    }


    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        return this.depTuple.getFunctionSymbols();
    }

    @Override
    public int hashCode() {
        return this.depTuple.hashCode();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        Cdt other = (Cdt) obj;
        if (this.depTuple == null) {
            if (other.depTuple != null) {
                return false;
            }
        } else if (!this.depTuple.equals(other.depTuple)) {
            return false;
        }
        return true;
    }

    @Override
    public Set<TRSVariable> getVariables() {
        return this.depTuple.getVariables();
    }

    @Override
    public TRSFunctionApplication getLeft() {
        return this.getRuleLHS();
    }

    @Override
    public FunctionSymbol getRootSymbol() {
        return this.depTuple.getRootSymbol();
    }

}
