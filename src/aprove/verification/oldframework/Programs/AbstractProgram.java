package aprove.verification.oldframework.Programs;

import aprove.prooftree.Export.Utility.*;

/**
 * An abstract class that represents a program. The purpose of this class
 * is to have a general interface to all type of programs (functional,
 * logic, imperative, and term rewriting systems).
 * @author Christian Haselbach
 * @version $Id$
 */

public abstract class AbstractProgram implements HTML_Able, LaTeX_Able {

    public static final int DEFAULT = 0;
    public static final int CONDITIONAL = AbstractProgram.DEFAULT + 1;
    public static final int LOGIC = AbstractProgram.CONDITIONAL + 1;
    public static final int EQUATIONAL = AbstractProgram.LOGIC + 1;
    public static final int SIMPLIFIED = AbstractProgram.EQUATIONAL + 1;
    public static final int A_TO_AC = AbstractProgram.SIMPLIFIED + 1;
    public static final int TO_TTT = AbstractProgram.A_TO_AC + 1;
    public static final int TO_CiME = AbstractProgram.TO_TTT + 1;
    public static final int TO_DEFAULT = AbstractProgram.TO_CiME + 1;
    public static final int NOTYPE = AbstractProgram.DEFAULT - 1;

    protected int type = AbstractProgram.DEFAULT;
    protected AbstractProgram origin = null;
    // Predefined stuff with certain semantics:
    protected Predefined predefined = null;

    public int getType() {
    return this.type;
    }

    public void setType(int t) {
    this.type = t;
    }

    public AbstractProgram getOrigin() {
      return this.origin;
    }

    public AbstractProgram getOldestOrigin() {
    if (this.getOrigin() == null) {
        return this;
    } else {
        return this.getOrigin().getOldestOrigin();
    }
    };

    public void setOrigin(AbstractProgram p) {
      this.origin = p;
    }

    public int getOriginType() {
    return this.origin == null ? AbstractProgram.NOTYPE : this.origin.getType();
    }

    public void setPredefined(Predefined predefined) {
    this.predefined = predefined;
    }

    public Predefined getPredefined() {
    return this.predefined;
    }

}
