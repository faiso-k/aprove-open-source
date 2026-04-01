package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations;


/**
 * Return from a method call location
 * @author marinag
 */
public class ReturnLocation extends Location {
    /**
     * @param id ID
     */
    public ReturnLocation(final int id) {
        super(id);
    }


    @Override
    public Object clone() {
        return new ReturnLocation(this.getId());
    }
}
