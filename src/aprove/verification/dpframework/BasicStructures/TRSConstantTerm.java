package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * A constant non-variable term.
 * @author cryingshadow
 * @version $Id$
 */
public final class TRSConstantTerm extends TRSFunctionApplication implements ConstantExpression {

    /**
     * @param f The function symbol of arity 0.
     */
    protected TRSConstantTerm(FunctionSymbol f) {
        super(f, ImmutableCreator.create(Collections.emptyList()));
        if (Globals.useAssertions) {
            assert (f.getArity() == 0) : "The arity of a constant expression must be 0!";
        }
    }

    /**
     * @param name The name of the constant.
     */
    protected TRSConstantTerm(String name) {
        this(FunctionSymbol.create(name, 0));
    }
    
    public String getValue() {
        return getFunctionSymbol().getName();
    }

    @Override
    public TRSConstantTerm applySubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        return this;
    }

    @Override
    public TRSConstantTerm applySubstitution(Substitution sigma) {
        return this;
    }

    @Override
    public TRSConstantTerm renameVariables(FreshVarGenerator gen) {
        return this;
    }

    @Override
    public ImmutablePair<TRSConstantTerm, Integer> renumberVariables(
        Map<TRSVariable, TRSVariable> map,
        String prefix,
        Integer nr
    ) {
        return new ImmutablePair<>(this, nr);
    }

    @Override
    public TRSConstantTerm replaceAll(FunctionSymbol replace, FunctionSymbol replacement) {
        if (Globals.useAssertions) {
            assert (replace.getArity() == replacement.getArity()) :
                "FunctionSymbol replacement with different arity detected!";
        }
        if (this.getRootSymbol().equals(replace)) {
            return new TRSConstantTerm(replacement);
        }
        return this;
    }

    @Override
    public TRSTerm tcap(ImmutableSet<FunctionSymbol> definedSymbols, FreshNameGenerator fng) {
        if (definedSymbols.contains(this.getRootSymbol())) {
            return new TRSVariable(fng.getFreshName(this.getName(), false));
        }
        return this;
    }

    @Override
    public TRSFunctionApplication tcapNe(Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR) {
        return this;
    }

    @Override
    protected TRSTerm helpLinearize(TRSVariable variable, Set<TRSVariable> toAvoid) {
        return this;
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
    protected TRSTerm processSubstitution(Substitution sigma) {
        return this;
    }

    @Override
    protected ImmutablePair<TRSTerm, Integer> tcap(Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR, Integer nr) {
        return TRSFunctionApplication.tcap(this, lhsR, nr);
    }

    @Override
    public ImmutablePair<TRSTerm, Integer> tcapE(
        Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR,
        Set<FunctionSymbol> ACs,
        Set<FunctionSymbol> Cs,
        Integer nr
    ) {
        return TRSFunctionApplication.tcapE(this, lhsR, ACs, Cs, nr);
    }
}
