package aprove.verification.oldframework.Bytecode.StateRepresentation;

/**
 * Classes implementing this interface can be notified when a state is deleted from its graph.
 * @author cotto
 */
public interface StateDeletionListener {

    /**
     * This method is called when the given state is deleted from its graph.
     * @param s the deleted state
     */
    void notifyStateDeletion(State s);

}
