package aprove.input.Programs.xtc;

import org.xml.sax.*;

public class ParserError extends Exception {

    private Locator locator;

    public ParserError(Locator locator, String message) {
        super(message);
        this.locator = locator;
    }

    public Locator getLocator() {
        return this.locator;
    }

}
