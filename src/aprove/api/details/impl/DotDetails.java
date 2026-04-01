package aprove.api.details.impl;

import aprove.prooftree.Export.Utility.*;

class DotDetails extends BaseDetails<DOT_Able> {

    public DotDetails() {
        super(DOT_Able.class);
    }

    @Override
    protected String details(DOT_Able t) {
        return t.toDOT();
    }
}
