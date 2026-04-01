package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/*
 * GeneralizedRule 8
 * replaces   f(p1,..,pn)=q & phi ==> psi
 * by p1 = x1 & .. & pn = xn & f(x1,..,xn) = q & phi ==> psi
 * if f is a defined functionsymbol and p1,..,pn not pairwise different variables
 */
public class InfRule8FuncVar extends InfRuleExpandLeft {

    @Override
    public InfRuleID getID() {
        return InfRuleID.VII;
    }

    @Override
    public String getLongName() {
        return "Rule VIII: Defined Symbol without Pairwise Different Variables";
    }

    @Override
    public String getName() {
        return "Rule VIII";
    }

    @Override
    public Mode actionForReducesTo(final ReducesTo reducesTo, final Implication implication, final Abortion aborter) {
        final FunctionSymbol f = reducesTo.getLeftRootSymbol();
        if (f != null && this.irc.isDefinedSymbol(f)) {
            // System.out.println("actionForReducesTo " + implication);
            final List<TRSVariable> vars = this.irc.getPDVaribales((TRSFunctionApplication) reducesTo.getLeft());
            if (vars == null) {
                this.irc.setMark(reducesTo);
                return Mode.ExpandDefined;
            }
        }
        return Mode.NoChange;
    }

    @Override
    public boolean createSubs() {
        return false;
    }

    @Override
    public Count expandCount(final ReducesTo reducesTo) {
        return reducesTo.getCount().incDepth();
    }

}
