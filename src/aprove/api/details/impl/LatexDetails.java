package aprove.api.details.impl;

import aprove.prooftree.Export.Utility.*;

class LatexDetails extends ExportableDetails<LaTeX_Able> {

    public LatexDetails() {
        super(LaTeX_Able.class);
    }

    @Override
    protected Export_Util exportUtil() {
        return new LaTeX_Util();
    }

    @Override
    protected String details(LaTeX_Able t) {
        return t.toLaTeX();
    }
}
