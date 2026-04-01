package aprove.prooftree.Export.Utility;

import immutables.*;

public class ExportableString implements Immutable, Exportable {

    private final String string;

    public ExportableString(String s) {
        this.string = s;
    }

    @Override
    public String export(Export_Util o) {
        return o.export(this.string);
    }

    @Override
    public String toString() {
        return this.string;
    }


}
