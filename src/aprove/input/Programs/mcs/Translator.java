package aprove.input.Programs.mcs;

import java.io.*;

import aprove.verification.dpframework.MCSProblem.*;
import aprove.verification.dpframework.MCSProblem.mcnp.*;
import aprove.verification.oldframework.Input.*;

/**
 * Parse a Monotonicity Constraint Transition System.
 *
 * @author fuhs
 */
public class Translator extends aprove.verification.oldframework.Input.Translator.TranslatorSkeleton {

    @Override
    public Language getLanguage() {
        return Language.MCS;
    }

    @Override
    public void translate(Reader reader) throws TranslationException {
        // TODO Auto-generated method stub
        BufferedReader bufReader = reader instanceof BufferedReader ?
                (BufferedReader) reader : new BufferedReader(reader);
        Program program = Program.create(bufReader);
        MCSProblem mcsProblem = program.toMCSProblem();
        this.setState(mcsProblem);
    }

}
