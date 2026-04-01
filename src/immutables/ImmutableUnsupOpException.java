package immutables;

public class ImmutableUnsupOpException extends UnsupportedOperationException {

    public ImmutableUnsupOpException() {
        super(Thread.currentThread().getStackTrace()[2].getMethodName()
            + " operation is not allowed in ImmutableStack "
            + Thread.currentThread().getStackTrace()[1].getClassName()
            + ".");
    }
}
