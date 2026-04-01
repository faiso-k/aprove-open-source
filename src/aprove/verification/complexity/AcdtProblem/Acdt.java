package aprove.verification.complexity.AcdtProblem;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.complexity.AcdtProblem.Utils.TupleDefinedPositions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Complexity Dependency Tuple
 */
public class Acdt implements Exportable, Immutable, HasFunctionSymbols {

    private final Rule depTuple;
    private final Rule baseRule;
    private final TupleDefinedPositions tdps;

    private Acdt(Rule depTuple, Rule baseRule, TupleDefinedPositions tdp) {
        if (Globals.useAssertions) {
            assert(depTuple.getRight() instanceof TRSFunctionApplication);
            List<TRSTerm> ruleArgs =
                ((TRSFunctionApplication)depTuple.getRight()).getArguments();
            TRSTerm baseRhs = baseRule.getRight();
            for (int i=0; i < ruleArgs.size(); i++) {
                TRSTerm arg = ruleArgs.get(i);
                TRSTerm subterm = baseRhs.getSubtermOrNull(tdp.getPosition(i));
                assert(arg instanceof TRSFunctionApplication);
                assert(subterm instanceof TRSFunctionApplication);
                /*
                 * XXX: Do we want to spend the time to check that the fArg =
                 * fSub^#\sigma?
                 */
            }
        }
        this.depTuple = depTuple;
        this.baseRule = baseRule;
        this.tdps = tdp;
    }

    public static Acdt create(Rule depTuple, Rule baseRule, TupleDefinedPositions tdp) {
        return new Acdt(depTuple, baseRule, tdp);
    }

    public static Acdt createFromRule(FreshNameGenerator fng, Rule rule, TRSSubstitution subst, TupleDefinedPositions tdps) {
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        TRSTerm ruleRhs = rule.getRight();
        for (TupleDefinedPosition tdp : tdps) {
            args.add(Acdt.makePairTerm(fng, (TRSFunctionApplication)ruleRhs.getSubterm(tdp.position)));
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
        return Acdt.create(Rule.create(pairLhs, pairRhs), rule, tdps);
    }

    public static Acdt createFromRule(FreshNameGenerator fng, Rule rule,
            Set<FunctionSymbol> definedSymbols) {
        TupleDefinedPositions tdps = TupleDefinedPositions.createFromRule(rule, definedSymbols);
        return Acdt.createFromRule(fng, rule, TRSSubstitution.EMPTY_SUBSTITUTION, tdps);
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


    public Acdt filter(BitSet removeTupleparts) {
        ArrayList<TRSFunctionApplication> oldArgs = this.getRuleRHSArgs();
        ArrayList<TRSFunctionApplication> newArgs =
            new ArrayList<TRSFunctionApplication>(removeTupleparts.size());
        int oldArity = oldArgs.size();
        for (int i=0; i < oldArity; i++) {
            if (!removeTupleparts.get(i)) {
                newArgs.add(oldArgs.get(i));
            }
        }

        FunctionSymbol newRhsFuncSym = FunctionSymbol.create(
                this.getRuleRHS().getRootSymbol().getName(),
                oldArity - removeTupleparts.cardinality());
        TRSFunctionApplication newRhs =
            TRSTerm.createFunctionApplication(newRhsFuncSym, newArgs);
        Rule newRule = Rule.create(this.getRuleLHS(), newRhs);

        TupleDefinedPositions newForest = this.tdps.filter(removeTupleparts);

        return new Acdt(newRule, this.baseRule, newForest);
    }

    public Acdt applySubstitution(TRSSubstitution sigma) {
        return new Acdt(this.depTuple.applySubstitution(sigma), this.baseRule, this.tdps);
    }

    public Rule getBaseRule() {
        return this.baseRule;
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

    @SuppressWarnings("unchecked")
    public ImmutableArrayList<TRSFunctionApplication> getRuleRHSArgs() {
        return (ImmutableArrayList)this.getRuleRHS().getArguments();
    }

    public TupleDefinedPositions getTupleDefPos() {
        return this.tdps;
    }

    @Override
    public String export(Export_Util eu) {
        ArrayList<Integer> repr = new ArrayList<Integer>(this.tdps.getDependencies());
        /* Index from 1 for human readable output */
        for (int i=0; i < repr.size(); i++) {
            repr.set(i, repr.get(i)+1);
        }
        return this.depTuple.export(eu) + " " + repr;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        Set<FunctionSymbol> result =
            this.depTuple.getFunctionSymbols();
        result.addAll(this.baseRule.getFunctionSymbols());
        return result;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.tdps == null) ? 0 : this.tdps.hashCode());
        result = prime * result
                + ((this.baseRule == null) ? 0 : this.baseRule.hashCode());
        result = prime * result
                + ((this.depTuple == null) ? 0 : this.depTuple.hashCode());
        return result;
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
        Acdt other = (Acdt) obj;
        if (this.tdps == null) {
            if (other.tdps != null) {
                return false;
            }
        } else if (!this.tdps.equals(other.tdps)) {
            return false;
        }
        if (this.baseRule == null) {
            if (other.baseRule != null) {
                return false;
            }
        } else if (!this.baseRule.equals(other.baseRule)) {
            return false;
        }
        if (this.depTuple == null) {
            if (other.depTuple != null) {
                return false;
            }
        } else if (!this.depTuple.equals(other.depTuple)) {
            return false;
        }
        return true;
    }

    public static class CdtCreateRes {
        public Acdt cdt;
        public Set<FunctionSymbol> pairSyms;
        public FunctionSymbol compoundSym;
    }

}
