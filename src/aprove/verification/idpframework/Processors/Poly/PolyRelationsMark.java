package aprove.verification.idpframework.Processors.Poly;

import aprove.verification.idpframework.Core.Utility.Marking.*;

/**
 *
 * @author MP
 */
public class PolyRelationsMark implements Mark<Disjunction<? extends RelationGraph<?>>> {

    public static final PolyRelationsMark MARK = new PolyRelationsMark();

    private PolyRelationsMark() {

    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return CompatibleMarkClasses.POLY_RELATIONS.isCompatible(mark);
    }

}
