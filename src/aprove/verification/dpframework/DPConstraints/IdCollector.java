package aprove.verification.dpframework.DPConstraints;

import java.util.*;

public class IdCollector extends DPConstraintVisitor {
    Collection<Object> col;

    public IdCollector(Collection<Object> col) {
        super();
        this.col = col;
    }

    @Override
    public void fcaseImplication(Implication implication) {
        this.col.add(implication.getId());
    }

    @Override
    public void fcaseReducesTo(ReducesTo reducesTo) {
        this.col.add(reducesTo.getId());
    }

}
