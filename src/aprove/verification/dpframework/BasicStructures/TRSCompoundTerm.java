package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * A compound function application.
 * @author cryingshadow
 * @version $Id$
 */
public final class TRSCompoundTerm extends TRSFunctionApplication implements CompoundExpression {

    /**
     * @param f The function symbol of arity > 0.
     * @param args The arguments. Its size must match the arity of the function symbol.
     */
    protected TRSCompoundTerm(FunctionSymbol f, ImmutableList<? extends TRSTerm> args) {
        super(f, args);
        if (Globals.useAssertions) {
            assert (f.getArity() > 0) : "The arity of a compound expression must be greater than 0!";
        }
    }

    @Override
    public TRSCompoundTerm applySubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        return this.applySubstitution(Substitution.toSubstitution(sigma));
    }

    @Override
    public final TRSCompoundTerm applySubstitution(Substitution sigma) {
        if (sigma instanceof TRSSubstitution) {
            if (((TRSSubstitution)sigma).isEmpty()) {
                return this;
            }
        }
        return this.processSubstitution(sigma);
    }

    @Override
    public TRSCompoundTerm processSubstitution(Substitution sigma) {
        ArrayList<TRSTerm> newArgs = null;
        for (int i = this.getArguments().size() - 1; i >= 0; i--) {
            final TRSTerm arg = this.getArguments().get(i);
            final TRSTerm newArg = arg.applySubstitution(sigma);
            if (arg != newArg) {
                if (newArgs == null) {
                    newArgs = new ArrayList<TRSTerm>(this.getArguments());
                }
                newArgs.set(i, newArg);
            }
        }
        if (newArgs != null) {
            return new TRSCompoundTerm(this.getRootSymbol(), ImmutableCreator.create(newArgs));
        } else {
            return this;
        }
    }

    @Override
    public TRSCompoundTerm renameVariables(aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator gen) {
        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(this.getArguments().size());
        for (TRSTerm arg : this.getArguments()) {
            newArgs.add(arg.renameVariables(gen));
        }
        return new TRSCompoundTerm(this.getRootSymbol(), ImmutableCreator.create(newArgs));
    }

    @Override
    public ImmutablePair<TRSCompoundTerm, Integer> renumberVariables(
        Map<TRSVariable, TRSVariable> map,
        String prefix,
        Integer nrParam
    ) {
        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(this.getArguments().size());
        Integer nr = nrParam;
        boolean changed = false;
        for (TRSTerm arg : this.getArguments()) {
            final ImmutablePair<? extends TRSTerm, Integer> resArg = arg.renumberVariables(map, prefix, nr);
            changed = changed || resArg.x != arg;
            newArgs.add(resArg.x);
            nr = resArg.y.intValue();
        }
        final TRSCompoundTerm res =
            changed ? new TRSCompoundTerm(this.getRootSymbol(), ImmutableCreator.create(newArgs)) : this;
        return new ImmutablePair<>(res, nr);
    }

    @Override
    public TRSFunctionApplication replaceAll(FunctionSymbol replace, FunctionSymbol replacement) {
        if (Globals.useAssertions) {
            assert (replace != null && replacement != null && replace.getArity() == replacement.getArity());
        }
        boolean changed = false;
        FunctionSymbol fSymbol = this.getRootSymbol();
        if (fSymbol.equals(replace)) {
            fSymbol = replacement;
            changed = true;
        }
        final ImmutableList<? extends TRSTerm> args = this.getArguments();
        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
        for (TRSTerm arg : args) {
            if (arg.isVariable()) {
                newArgs.add(arg);
            }
            else {
                final TRSFunctionApplication newArg = ((TRSFunctionApplication)arg).replaceAll(replace, replacement);
                if (newArg != arg) {
                    changed = true;
                }
                newArgs.add(newArg);
            }
        }
        if (changed) {
            return TRSTerm.createFunctionApplication(fSymbol, newArgs);
        } else {
            return this;
        }
    }

    @Override
    @SuppressWarnings("unchecked")
    public TRSCompoundTerm setArguments(ImmutableList<? extends Expression> args) {
        return new TRSCompoundTerm(this.getRootSymbol(), (ImmutableList<? extends TRSTerm>)args);
    }

    @Override
    public TRSTerm tcap(ImmutableSet<FunctionSymbol> definedSymbols, FreshNameGenerator fng) {
        if (definedSymbols.contains(this.getRootSymbol())) {
            return new TRSVariable(fng.getFreshName(this.getName(), false));
        }
        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(this.getArguments().size());
        for (TRSTerm arg : this.getArguments()) {
            newArgs.add(arg.tcap(definedSymbols, fng));
        }
        return TRSTerm.createFunctionApplication(this.getRootSymbol(), ImmutableCreator.create(newArgs));
    }

    @Override
    public final TRSFunctionApplication tcapNe(Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR) {
        if (Globals.useAssertions) {
            assert (TRSTerm.tcapAssertCheck(lhsR));
        }
        final List<TRSTerm> result = new ArrayList<TRSTerm>(this.getArguments().size());
        Integer nr = TRSTerm.STANDARD_NUMBER;
        for (TRSTerm arg : this.getArguments()) {
            final ImmutablePair<TRSTerm, Integer> res = arg.tcap(lhsR, nr);
            if (Globals.useAssertions) {
                assert (arg.equals(res.x) || nr != res.y);
            }
            nr = res.y;
            result.add(res.x);
        }
        if (nr == TRSTerm.STANDARD_NUMBER) {  // nothing was capped
            return this;
        } else {
            return TRSTerm.createFunctionApplication(this.getRootSymbol(), result);
        }
    }

    /**
     * Help-method for the method "linearize(Variable)" in the super-class "Term".
     * @author Sebastian Weise
     */
    @Override
    protected TRSCompoundTerm helpLinearize(TRSVariable variable, Set<TRSVariable> toAvoid) {
        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
        for (TRSTerm actArg : this.getArguments()) {
            newArgs.add(actArg.helpLinearize(variable, toAvoid));
        }
        return new TRSCompoundTerm(this.getRootSymbol(), ImmutableCreator.create(newArgs));
    }

    @Override
    protected ImmutablePair<TRSTerm, Integer> icapQRst(
        QTermSet Q,
        Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR,
        TRSFunctionApplication s,
        Integer startNr
    ) {
        return TRSFunctionApplication.icapQRst(this, Q, lhsR, s, startNr);
    }

    @Override
    protected ImmutablePair<TRSTerm, Integer> tcap(
        Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR,
        Integer startNr
    ) {
        return TRSFunctionApplication.tcap(this, lhsR, startNr);
    }

    @Override
    public ImmutablePair<TRSTerm, Integer> tcapE(
        Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR,
        Set<FunctionSymbol> ACs,
        Set<FunctionSymbol> Cs,
        Integer startNr
    ) {
        return TRSFunctionApplication.tcapE(this, lhsR, ACs, Cs, startNr);
    }
}
