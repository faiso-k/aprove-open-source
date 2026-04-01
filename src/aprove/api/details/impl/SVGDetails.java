package aprove.api.details.impl;

import aprove.prooftree.Export.Utility.*;

class SVGDetails extends BaseDetails<SVG_Able> {

    public SVGDetails() {
        super(SVG_Able.class);
    }

    @Override
    protected String details(final SVG_Able t) {
        return t.toSVG().getAbsolutePath();
    }
}
