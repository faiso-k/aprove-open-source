package aprove.input.Programs.prolog.graph;

import aprove.input.Programs.prolog.structure.*;

/**
 * NumberedCut.<br><br>
 *
 * Created: Sep 3, 2008<br>
 * Last modified: Sep 3, 2008
 *
 * @author cryingshadow
 * @version $Id$
 */
public class LabeledCut extends PrologTerm {

    private final int number;

    /**
     * @param name
     * @throws IllegalArgumentException
     */
    public LabeledCut(final int number) throws IllegalArgumentException {
        super("!_" + number);
        this.number = number;
    }

    @Override
    public boolean equals(final Object o) {
        if (o instanceof LabeledCut) {
            return this.getNumber() == ((LabeledCut) o).getNumber();
        }
        return false;
    }

    public int getNumber() {
        return this.number;
    }

    @Override
    public int hashCode() {
        return this.getNumber() * 17;
    }

    @Override
    public boolean isCut() {
        return true;
    }

    @Override
    public String toLaTeX(final KnowledgeBase kb) {
        return "\\Fcut_{" + this.getNumber() + "}";
    }

    @Override
    public String toString() {
        return "!_" + this.getNumber();
    }

}
