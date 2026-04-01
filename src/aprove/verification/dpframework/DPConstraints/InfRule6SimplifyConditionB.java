package aprove.verification.dpframework.DPConstraints;

/*
 * Rule6 SimplyfyCondition
 * replace    phi & (\/y1...yn.phi' ==> psi') ==> psi
 * with       phi & psi'*sigma ==> psi
 *
 * but only if       phi'*sigma <== phi
 *
 * for every A in phi' there exist a B in phi with A*sigma <== B
 * to As does share the same B
 */
public class InfRule6SimplifyConditionB extends InfRule6SimplifyConditionA {

    @Override
    public InfRuleID getID() {
        return InfRuleID.VI;
    }

    @Override
    public String getLongName() {
        return "Rule VIB: Simpliyfy Condition (multiset)";
    }

    @Override
    public String getName() {
        return "Rule VIB";
    }

    public InfRule6SimplifyConditionB() {
        super();
        this.multiSet = false;
    }

}
