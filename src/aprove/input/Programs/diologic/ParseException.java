/**
 *
 * @author weidmann
 * @version $Id$
 */
package aprove.input.Programs.diologic;

/* ParseException mainly differs from ParserException in that it extends
 * RuntimeException instead of Exception.
 */

import aprove.input.Generated.diologic.node.*;

public class ParseException extends RuntimeException {
    private Token token;

    public ParseException(String message) {
        super(message);
    }

    public ParseException(@SuppressWarnings("hiding") Token token, String  message)
    {
        super(message);
        this.token = token;
    }


    public Token getToken() {
        return this.token;
    }
}
