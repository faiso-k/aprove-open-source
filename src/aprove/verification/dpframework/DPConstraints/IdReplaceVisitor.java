package aprove.verification.dpframework.DPConstraints;

import java.util.*;

public class IdReplaceVisitor extends DPConstraintVisitor {
    Map<Object, Object> map;

    public IdReplaceVisitor(Map<Object, Object> map) {
        super();
        this.map = map;
    }

    @Override
    public TRSVisitable caseImplication(Implication implication) {
        Object id = this.map.get(implication.getId());
        if (id != null) {
            return Implication.create(
                id,
                implication.getQuantor(),
                implication.getConditions(),
                implication.getConclusion(),
                implication.getData());
        } else {
            return implication;
        }
    }

    @Override
    public TRSVisitable caseReducesTo(ReducesTo reducesTo) {
        Object id = this.map.get(reducesTo.getId());
        if (id != null) {
            return ReducesTo.create(
                reducesTo.getLeft(),
                reducesTo.getRight(),
                reducesTo.getParentFunc(),
                reducesTo.getCount(),
                id);
        } else {
            return reducesTo;
        }
    }

}
