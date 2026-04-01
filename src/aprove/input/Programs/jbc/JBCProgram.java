package aprove.input.Programs.jbc;

import aprove.verification.oldframework.Input.*;

/**
 * This class represents the program handed to us to analyze.
 *
 * @author Marc Brockschmidt
 */
public class JBCProgram {
    /**
     * An input object giving us the program to analyze.
     */
    private final Input input;

    /**
     * @param inputParam an input object giving us the classfile to regard as starting file.
     */
    public JBCProgram(final Input inputParam) {
        this.input = inputParam;
    }

    /**
     * @return the input defining the program to analyze
     */
    public Input getInput() {
        return this.input;
    }
}
