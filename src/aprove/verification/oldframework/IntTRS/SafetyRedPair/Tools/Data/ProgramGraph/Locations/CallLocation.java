package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations;


/**
 * Method call location
 * @author marinag
 */
public class CallLocation extends Location {
    /**
     * Return location
     */
    private Location returnLocation = null;
    private Location branchLocation = null;

    /**
     * Call name
     */
    private final String callId;

    /**
     * @param id ID
     * @param callId call name
     */
    public CallLocation(
        final int id,
        final String callId)
    {
        super(id);
        this.callId = callId;
    }

    public CallLocation(final int id, final Location branchLocation, final Location returnLocation, final String callId)
    {
        super(id);
        this.callId = callId;
        this.branchLocation = branchLocation;
        this.returnLocation = returnLocation;
    }


    /**
     * @return the set of possible locations to return to from this call
     */
    public Location getReturnLocation() {
        return this.returnLocation;
    }

    public Location getBranchLocation() {
        return this.branchLocation;
    }

    /**
     * @return call name
     */
    public String getCallId() {
        return this.callId;
    }

    @Override
    public Object clone() {
        final CallLocation l = new CallLocation(this.getId(), this.branchLocation, this.returnLocation, this.callId);

        return l;
    }

    /**
     * @param returnLocation set of possible locations to return to from this call
     */
    public void setLocations(final Location returnLocation, final Location branchLocation) {
        this.returnLocation = returnLocation;
    }

    @Override
    public String toString() {
        return super.toString() + " " + this.callId;
    }
}
