package aprove.input.Programs.prolog.structure;

import java.util.*;

/**
 * NameWalker.<br><br>
 *
 * Created: Mar 30, 2007<br>
 * Last modified: Mar 30, 2007
 *
 * @author cryingshadow
 * @version $Id$
 */
public class NameWalker implements TermWalker {

    /**
     * The set of names to gather.
     */
    private final Set<String> result;

    /**
     * Standard constructor.
     */
    public NameWalker() {
        this.result = new LinkedHashSet<String>();
    }

    /**
     * Returns the gathered set of names.
     * @return The gathered set of names.
     */
    public Set<String> getResult() {
        return this.result;
    }

    @Override
    public boolean goDeeper(final PrologTerm term) {
        return true;
    }

    @Override
    public boolean isApplicable(final PrologTerm term) {
        return true;
    }

    @Override
    public void performAction(final PrologTerm term) {
        this.result.add(term.getName());
    }

}
