package aprove.verification.dpframework.BasicStructures.Utility;

/**
 * @author Matthias Sondermann
 * @veriosn $Id$
 *
 * Enum to handle strictness modes of many processors
 */
public enum PoloStrictMode {

    AUTOSTRICT("AUTOSTRICT"),
    ALLSTRICT("ALLSTRICT"),
    SEARCHSTRICT("SEARCHSTRICT");


    final String name;

    private PoloStrictMode(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return this.name;
    }
}
