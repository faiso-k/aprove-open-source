package aprove.verification.oldframework.Input.TypeAnalyzers;

import aprove.verification.oldframework.Input.*;

/**
 * Determine type of program and parse.
 * @author nowonder
 * @version $Id$
 */

public interface TypeAnalyzer {

    public TypedInput analyze(Input input) throws ParserErrorsSourceException;

}
