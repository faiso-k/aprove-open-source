/*
 * Created on Jul 1, 2003
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package aprove.verification.oldframework.Input;

import java.io.*;

import aprove.verification.oldframework.Rewriting.*;

/**
 * Use this ObjectInputStream in order to synchronize with a porgramm that could be altered
 * @author eugenyu
 *
 *
 */
public class InputStreamWithProg extends ObjectInputStream {

    protected Program prog;

    /**
     * @param in
     * @param p is the program that holds symbols which should be assigned to the term to be loaded
     * @throws java.io.IOException
     */
    public InputStreamWithProg(InputStream in, Program p) throws IOException {
        super(in);
        this.prog = p;
    }

    /**
     * @param p is the program that holds symbols which should be assigned to the term to be loaded
     * @throws java.io.IOException
     * @throws java.lang.SecurityException
     */
    public InputStreamWithProg(Program p) throws IOException, SecurityException {
        super();
        this.prog = p;
    }

    public Program getProgram(){
        return this.prog;
    }

}
