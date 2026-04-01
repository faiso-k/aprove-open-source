package aprove.api.details.impl;

import aprove.prooftree.Export.Utility.*;

class HtmlDetails extends ExportableDetails<HTML_Able> {

    public HtmlDetails() {
        super(HTML_Able.class);
    }

    @Override
    protected Export_Util exportUtil() {
        return new HTML_Util();
    }

    @Override
    protected String details(HTML_Able t) {
        return t.toHTML();
    }
}
