package aprove.api.details.impl;

public abstract class BaseDetails<T> {

    private final Class<T> itsInterface;

    public BaseDetails(Class<T> itsInterface) {
        this.itsInterface = itsInterface;
    }

    public boolean isSupported(Object o) {
        return this.itsInterface.isInstance(o);
    }

    public String getDetails(Object o) {
        if (this.itsInterface.isInstance(o)) {
            return this.details(this.itsInterface.cast(o));
        } else if (o == null) {
            return "(null)";
        } else {
            return this.notAnInstance(o);
        }
    }

    protected String notAnInstance(Object o) {
        return "(" + o.getClass().getSimpleName()
               + " is not "
               +
               this.itsInterface.getSimpleName()
               + ")";
    }

    protected abstract String details(T t);
}
