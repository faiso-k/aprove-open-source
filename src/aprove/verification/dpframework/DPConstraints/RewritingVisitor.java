package aprove.verification.dpframework.DPConstraints;

import aprove.verification.dpframework.BasicStructures.*;

public class RewritingVisitor extends DPConstraintVisitor {

    private TRSTerm replace;
    private TRSTerm replacement;

    public RewritingVisitor(TRSTerm replace, TRSTerm replacement) {
        super();
        this.replace = replace;
        this.replacement = replacement;
    }

    @Override
    public TRSVisitable casePredicate(Predicate predicate) {
        return predicate.replaceAll(this.replace, this.replacement);
    }

    @Override
    public TRSVisitable caseReducesTo(ReducesTo reducesTo) {
        return reducesTo.replaceAll(this.replace, this.replacement);
    }

}
