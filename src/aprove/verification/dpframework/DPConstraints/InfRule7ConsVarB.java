package aprove.verification.dpframework.DPConstraints;

import aprove.verification.dpframework.BasicStructures.*;

/*
 * Rule7
 * replace f(p1,...,pn) = x & phi ==> psi
 * by      p1 = x1 & .. & pn=xn & phi*sigma ==> psi*sigma
 * with    sigma = [x/f(x1,..,xn)]
 *
 * deprecated
 *
 */
public class InfRule7ConsVarB extends InfRule7ConsVarA {

    @Override
    public InfRuleID getID() {
        return InfRuleID.DEPRECATED;
    }

    @Override
    public String getLongName() {
        return "Rule VIIB: Constructor and Variable (full)";
    }

    @Override
    public String getName() {
        return "Rule VIIB";
    }

    public boolean checkLeftOccur(InfRuleContext irc, TRSVariable x, Implication implication) {
        return false;
    }

}
