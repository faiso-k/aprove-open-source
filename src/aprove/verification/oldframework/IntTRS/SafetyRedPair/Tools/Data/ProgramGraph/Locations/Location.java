package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations;

import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Program graph location, identified by a unique LocationID
 * @author marinag
 */
public class Location extends Node<LocationID> implements Cloneable, PrettyStringable {

    /**
     * @param id ID
     */
    public Location(final int id) {
        super(LocationID.create(id));
    }


    @Override
    public Object clone() {
        return new Location(this.getId());
    }

    @Override
    public boolean equals(final Object obj) {
        if (obj == null || !(obj instanceof Location)) {
            return false;
        }

        final Location loc = (Location) obj;

        if (this == loc) {
            return true;
        }

        return loc.getId() == this.getId();
    }


    @Override
    public int hashCode() {
        return this.getId();
    }

    @Override
    public String prettyToString() {
        return "L" + String.valueOf(this.getId());
    }

    @Override
    public String toString() {
        return this.prettyToString();
    }

    public boolean isBefore(final Location l) {
        return this.getId() < l.getId();
    }

    public int getId() {
        return this.getObject().getId();
    }

    @Override
    public int compareTo(final Node<?> node) {

        if (this.equals(node)) {
            return 0;
        }

        assert node instanceof Location;
        final Location l = (Location) node;

        return this.isBefore(l) ? -1 : 1;
    }
}
