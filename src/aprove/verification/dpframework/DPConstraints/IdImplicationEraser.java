package aprove.verification.dpframework.DPConstraints;

public class IdImplicationEraser extends DPConstraintVisitor {
    Object id;
    boolean change;

    @Override
    public TRSVisitable caseImplication(Implication implication) {
        if (this.id == implication.getId()) {
            this.change = true;
            return ConstraintSet.emptySet;
        } else {
            return implication;
        }
    }

    public IdImplicationEraser(Object id) {
        super();
        this.id = id;
        this.change = false;
    }

    public boolean isChange() {
        return this.change;
    }

}
