package aprove.api.details.impl;

import aprove.prooftree.Export.Utility.*;

class DotModernDetails extends BaseDetails<DOTmodern_Able> {

    public DotModernDetails() {
        super(DOTmodern_Able.class);
    }

    @Override
    protected String details(final DOTmodern_Able t) {
        return t.toDOT();
    }
}
