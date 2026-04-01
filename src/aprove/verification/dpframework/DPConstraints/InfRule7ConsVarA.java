package aprove.verification.dpframework.DPConstraints;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/*
 * Rule7
 * replace f(p1,...,pn) = x & phi ==> psi
 * by      p1 = x1 & .. & pn=xn & phi*sigma ==> psi*sigma
 * with    sigma = [x/f(x1,..,xn)]
 * if f is a constructor
 * if phi does not contain a reducesTo where x occurs in the left-hand side
 * in an argument of defined symbol
 *
 * deprecated
 *
 */
public class InfRule7ConsVarA extends InfRuleExpandLeft {

    @Override
    public InfRuleID getID() {
        return InfRuleID.DEPRECATED;
    }

    @Override
    public String getLongName() {
        return "Rule VIIA: Constructor and Variable (x does not occur in the left-hand side)";
    }

    @Override
    public String getName() {
        return "Rule VIIA";
    }

    @Override
    public Mode actionForReducesTo(ReducesTo reducesTo, Implication implication, Abortion aborter) {
        FunctionSymbol f = reducesTo.getLeftRootSymbol();
        if (f != null && !this.irc.isDefinedSymbol(f)) {
            if (reducesTo.getRight().isVariable()) {
                if (this.checkLeftOccur((TRSVariable) reducesTo.getRight(), implication)) {
                    return Mode.NoChange;
                }
                this.irc.setMark(reducesTo);
                return Mode.Expand;
            }
        }
        return Mode.NoChange;
    }

    @Override
    public boolean createSubs() {
        return true;
    }

    @Override
    public Count expandCount(ReducesTo reducesTo) {
        return reducesTo.getCount();
    }

}
