package aprove.input.Programs.prolog;

import aprove.input.Programs.prolog.structure.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author cryingshadow
 * This class exists just to avoid warnings about casts and generics...
 */
public class ParsedProlog extends Pair<PrologProgram, PrologQuery> {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = 4569061428482804780L;

    /**
     * @param p The program.
     * @param q The query.
     */
    public ParsedProlog(final PrologProgram p, final PrologQuery q) {
        super(p, q);
    }

}
