package aprove.input.Formulas.pl;

import java.io.*;
import java.util.*;

import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * Parser for formulas which are assumed to be separated by line feeds.
 *
 * @author dickmeis
 * @version $Id$
 */

public class FormulaParser {

    protected  static final String NO_PROGRAM_LOADED_ERROR_MESSAGE ="Please load a program first.";

    protected Translator translator;

    protected FormulaParser(Program program){
        this.translator = new Translator();
        this.translator.setContext(program);
    }

    /**
     * Creates a FormulaParser which has a program as context
     * (if the program is not null)
     *
     * @param program which is used as context for parsing
     * @return the FormulaParser
     * @throws Exception if the program is null
     */
    static public FormulaParser createFormulaParser(Program program) throws Exception{
        if (program == null){
            throw new Exception(FormulaParser.NO_PROGRAM_LOADED_ERROR_MESSAGE);
        }
        return new FormulaParser(program);
    }

    /**
     * Parses a string into formulas.
     * The fomulas are assumed to be separated by line feeds.
     * The given program serves as context for the pasing.
     *
     * @param input that should be parsed. The fomulas are assumed to be separated by line feeds.
     * @return the parsed formulas
     */
    public ArrayList<Formula> parseFormula(String input) throws Exception {
        ByteArrayInputStream byteArrayInputStream = new ByteArrayInputStream(input.getBytes());
        BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(byteArrayInputStream));

        return this.parseFormula(bufferedReader);
    }

    /**
     * Parses the input of a BufferedReader into formulas.
     * The fomulas are assumed to be separated by line feeds.
     * The given program serves as context for the pasing.
     *
     * @param bufferedReader whos input should be parsed.
     *          The fomulas are assumed to be separated by line feeds.
     * @return the parsed formulas
     */
    public ArrayList<Formula> parseFormula(BufferedReader bufferedReader) throws Exception {
        ArrayList<Formula> formulas = new ArrayList<Formula>();
        String line;

        line = bufferedReader.readLine();
        while(line != null) {
            if (!line.equals("")){
                this.translator.translate(line);
                Formula formula = this.translator.getFormula();

                formulas.add(formula);
            }
            line = bufferedReader.readLine();
        }

        return formulas;
    }

}
