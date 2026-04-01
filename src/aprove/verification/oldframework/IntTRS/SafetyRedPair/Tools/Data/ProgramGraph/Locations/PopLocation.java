package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations;


/**
 * Stack pop location
 * @author marinag
 */
public class PopLocation extends Location {

    String var;

    /**
     * @param id ID
     * @param var the name of the variable to which the popped value shall be assigned
     */
    public PopLocation(final Integer id, final String var) {
        super(id);
        this.var = var;
    }


    @Override
    public Object clone() {
        return new PopLocation(this.getId(), this.getVariable());
    }

    public String getVariable() {
        return this.var;
    }
}
