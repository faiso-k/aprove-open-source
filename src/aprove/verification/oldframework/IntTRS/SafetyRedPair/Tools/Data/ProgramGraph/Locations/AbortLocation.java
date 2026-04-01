package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations;


/**
 * Abort location (represents an error location)
 * @author marinag
 */
public class AbortLocation extends Location {

    /**
     *
     */
    private static final long serialVersionUID = -2382492566569801363L;

    /**
     * @param id ID number
     */
    public AbortLocation(final int id) {
        super(id);
    }

    @Override
    public Object clone() {
        return new AbortLocation(this.getId());
    }

    @Override
    public String prettyToString() {
        return "E" + String.valueOf(this.getId());
    }
}
