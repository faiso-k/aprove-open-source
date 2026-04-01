package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations;



/**
 * Program location identifier, basically just a unique integer
 * @author marinag
 */
public final class LocationID {

    /**
     * IDs
     */
    final private Integer id;

    /**
     * Creates a LocationID with the given IDs
     * @param ids IDs
     */
    private LocationID(final Integer id) {
        this.id = id;
    }

    /**
     * @param id ID
     * @return LocationID with the given ID
     */
    public static LocationID create(final int id) {
        return new LocationID(id);
    }

    @Override
    public String toString() {
        return String.valueOf(this.id);
    }

    public int getId() {
        return this.id;
    }
}
