package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * An InfRuleContext offers some global infos for the InfRules.
 * @author swiste
 */
public interface InfRuleContext<C extends GPolyCoeff> {

    boolean isDefinedSymbol(FunctionSymbol f);

    boolean isNormal(TRSTerm t);

    boolean occursOnce(TRSVariable v);

    boolean occursNTimes(TRSVariable v, int n);

    // Set<FunctionSymbol> getDefiniedSymbols();
    // Set<FunctionSymbol> getConstructorSymbols();
    // Set<FunctionSymbol> getConstructorNoHeadSymbols();
    Set<? extends GeneralizedRule> getRules();

    Set<? extends GeneralizedRule> getRulesFor(FunctionSymbol f);

    TRSVariable getFreshVariable();

    TRSVariable getFreshVariable(TRSVariable replace);

    List<TRSVariable> getFreshVariables(int i);

    TRSSubstitution getFreshRenamingFor(Collection<TRSVariable> vars);

    Object getInductionBlockId();

    int getNextRuleNumber();

    int getRuleCount();

    List<TRSVariable> getPDVaribales(TRSFunctionApplication fal);

    void setMark(Exportable mark);

    int getInductionCount();

    boolean isNonRecursive(FunctionSymbol f);

    boolean isTailRecursive(FunctionSymbol f);

    public GInterpretation<C> getPolyInterpretation();

    public void show(List<Implication> cs);

    public boolean isIdpMode();

    boolean isDeterminisic(FunctionSymbol rootSymbol, Abortion aborter) throws AbortionException;

    boolean isDeterministic(TRSTerm arg, Abortion aborter) throws AbortionException;

    boolean isGround(TRSTerm left);

    Set<FunctionSymbol> getConstructorNoHeadSymbols();

    int getRewritingCount();

}
