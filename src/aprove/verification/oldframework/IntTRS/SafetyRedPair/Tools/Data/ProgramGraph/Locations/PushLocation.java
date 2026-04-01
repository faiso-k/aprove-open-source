package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations;


/**
 * Stack push location
 * @author marinag
 */
public class PushLocation extends Location {
    /**
     * The pushed variable
     */
    String var;

    /**
     * @param ids IDs
     * @param vat the pushed variable
     */
    public PushLocation(
        final int id,
        final String var)
    {
        super(id);
        this.var = var;
    }

    @Override
    public Object clone() {
        return new PushLocation(this.getId(), this.var);
    }

    @Override
    public String toString() {
        return super.toString()
            + " "
            + this.var.toString();
    }

    public String getPushedVariable() {
        return this.var;
    }
}
