/*
 * Created on 03.09.2004
 */
package aprove.input;

import java.io.*;
import java.util.*;

import aprove.input.Generated.pl.node.*;
import aprove.input.Generated.pl.parser.*;
import aprove.input.Formulas.pl.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * @author rabe
 */
public class CommentLineAnalyzer {

    protected Reader            reader;

    protected String            comment;

    protected String            formulaIndicator;

    protected Program            program;

    protected int                 lineOfParserException;

    public CommentLineAnalyzer( Reader reader, String comment, String formulaIndicator, Program program) {

        this.reader                 = reader;
        this.comment                 = comment;
        this.formulaIndicator         = formulaIndicator;
        this.program                   = program;
    }

    public  List<Formula> checkForFormulas() throws Exception {

        List<Formula> returnValue = new Vector<Formula>();

        BufferedReader bufferedReader = new BufferedReader(this.reader);

        String pattern = this.comment + "\\s*+"+this.formulaIndicator+".*";
        String replacePattern = this.comment + "\\s*+"+this.formulaIndicator;

        try {

            String line;
            this.lineOfParserException = 1;

            while( (line = bufferedReader.readLine()) != null ) {
                if(line.matches(pattern) && !line.equals("")) {
                    returnValue.add(this.parseFormulas(line.replaceAll(replacePattern,"").trim()));
                }
                this.lineOfParserException += 1;
            }

        } catch (IOException e) {
            e.printStackTrace();
        } catch (ParserException e) {
            Token newToken = (Token)e.getToken().clone();
            newToken.setLine(this.lineOfParserException);
            String newMessage = "["+this.lineOfParserException+","+newToken.getPos()+"]"+e.getMessage().split("\\]",2)[1];
            throw new ParserException(newToken,newMessage);
        }

           return returnValue;
    }

    protected Formula parseFormulas(String input) throws Exception {

        Translator translator = new Translator();
        translator.setContext(this.program);

        translator.translate(input);

        return translator.getFormula();

    }

}
