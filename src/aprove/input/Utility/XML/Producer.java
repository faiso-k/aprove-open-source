package aprove.input.Utility.XML;

public abstract class Producer<T> {
    private final Consumer<T> parent;

    public Producer(Consumer<T> parent) {
        this.parent = parent;
    }

    /**
     * Returns the result, if it can already be created and no error occurred.
     * @return
     */
    public abstract T getResult();

    protected final void produce() {
        this.parent.consume(this.getResult());
    }
}