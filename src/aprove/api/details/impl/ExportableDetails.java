package aprove.api.details.impl;

import aprove.prooftree.Export.Utility.*;

abstract class ExportableDetails<T> extends BaseDetails<T> {

    public ExportableDetails(Class<T> itsInterface) {
        super(itsInterface);
    }

    @Override
    public boolean isSupported(Object o) {
        return super.isSupported(o) || (o instanceof Exportable);
    }

    @Override
    protected String notAnInstance(Object o) {
        if (o instanceof Exportable) {
            return ((Exportable) o).export(this.exportUtil());
        } else {
            return super.notAnInstance(o);
        }
    }

    protected abstract Export_Util exportUtil();
}
