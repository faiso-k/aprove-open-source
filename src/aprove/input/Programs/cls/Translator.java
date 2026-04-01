/*
 * Created on 10.10.2005
 * This class starts the Lexer to determine if the
 * given input is a valid one based on the actual
 * grammar. If the Lexer was successful it has
 * transformed the input into a tree and FullPass
 * collects the information out of this tree.
 * FullPass will also find syntactical errors like
 * Variable Application, for details see class FullPass.
 * If FullPass was successful, the ObligationCreator will
 * determine if the collected information form a valid
 * combination, since not all kind of rules and flags can
 * be used together, so here it is kind of a semantical
 * check. If all goes well a new proof obligation will be
 * created.
 */

package aprove.input.Programs.cls;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.input.Generated.cls.lexer.*;
import aprove.input.Generated.cls.node.*;
import aprove.input.Generated.cls.parser.*;
import aprove.input.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Input.*;

/**
 *
 * @author stein
 * @version $Id$
 *
 */

/*
 * The object fullpass needs to be declared here on top level
 * to be able to give this object as parameter to
 * the ObligationCretaor. Otherwise all the information
 * would have to be copied into this class and afterwards
 * given to the ObligationCreator.
 */
public class Translator extends aprove.verification.oldframework.Input.Translator.TranslatorSkeleton {

    Set<TRSVariable> variables = new LinkedHashSet<TRSVariable>();
    private FullPass fullpass = null;
    Language language =null;

    private static Logger logger = Logger.getLogger("aprove.InputModels.Programs.trs.Translator");

    @Override
    public Language getLanguage() {
        return this.language;
    }

    @Override
    public void translate(Reader reader) {
        this.setState(null);
        try {
            Lexer lexer = new Lexer(new PushbackReader(reader,1024));
            Parser parser = new Parser(lexer);
            Start tree = parser.parse();
            this.translateDecls(tree);
        }
        catch (Exception e) {
            e.printStackTrace();
            ParseError pe = new ParseError(ParseError.ERROR);
            if (e instanceof ParserException) {
                Token t = ((ParserException) e).getToken();
                pe.setToken(t.toString().trim());
                pe.setPosition(t.getLine(), t.getPos());
                pe.setMessage(e.getMessage());
            } else if (e instanceof LexerException) {
                pe.setMessage("Lexer exception: " + e.getMessage());
            } else {
                pe.setMessage("Unknown error: " + e.getMessage());
                if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                    e.printStackTrace();
                }
            }
            this.getErrors().add(pe);
        }

 /*       //TODO delete after testing
        //testMethod(tr);

        // If errors is not empty at this point the class Fullpass has detected
        // something invalid. Since the input is not even syntactical correct, no
        // effort is made to try and build a new proof obligation out of it.
        // Therefore state is null.
        // Type is set to QTRS to avoid null pointer exceptions,
        // QTRS is basicly arbitrarily choosen, it is the "simplest" proof obligation.
*/

        if(!this.getErrors().isEmpty())
        {
            this.setState(null);
            this.language = Language.QTRS;

            if(Globals.DEBUG_PATWIE) {
                System.err.println(this.getErrors().toString());
                System.err.println("Fix Errors first, number one!");
            }
        }
        else{
            ObligationCreator obligationCreator = new ObligationCreator(this.fullpass);
            this.setState(obligationCreator.buildObligation());
            this.language = obligationCreator.getLanguage();

            if (this.getState() == null && this.getErrors().isEmpty()){
                List<ParseError> errorMessages = obligationCreator.getErrors();
                for(ParseError er : errorMessages) {
                    this.getErrors().add(er);
                }
            }
        }
        if(!this.getErrors().isEmpty() && Translator.logger.isLoggable(Level.SEVERE)) {
            Translator.logger.log(Level.SEVERE, this.getErrors().toString());
        }
    }

    public void translateDecls(Start tree) {
        this.fullpass = new FullPass();
        tree.apply(this.fullpass);
        this.setErrors(this.fullpass.getErrors());
/*
        //TODO delete after testing
        this.simpleRules = fullpass.getSimpleRules();
        this.relativeRules = fullpass.getRelativeRules();
        this.conditionalRules = fullpass.getConditionalRules();
        this.contextSensitiveRuleList = fullpass.getContextSensitiveRules();
        this.pairs = fullpass.getPairs();
        this.equationsSet = fullpass.getEquations();
        this.qFunctionApplicationSet = fullpass.getQFunctionApplications();
        this.minimal = fullpass.getMinimal();
        this.innermost = fullpass.getInnermost();

*/
    }

/*
    //TODO delete after testing
    // All collected information are given out on console
    private static void testMethod(Translator tr) {
        if(!tr.variables.isEmpty()) {
            System.err.println("VARIABLES:");
            System.err.println(tr.variables.toString());
        }
        if(tr.simpleRules!=null) {
            System.err.println("SIMPLE RULES:");
            System.err.println(tr.simpleRules.toString());
        }
        if(tr.relativeRules!=null) {
            System.err.println("RELATIVE RULES:");
            System.err.println(tr.relativeRules.toString());
        }
        if(tr.conditionalRules!=null) {
            System.err.println("CONDITIONAL RULES:");
            System.err.println(tr.conditionalRules.toString());
        }
        if(tr.contextSensitiveRuleList!=null) {
            System.err.println("CONTEXT SENSITIVE RULES:");
            System.err.println(tr.contextSensitiveRuleList.toString());
        }
        if(tr.pairs!=null) {
            System.err.println("PAIRS:");
            System.err.println(tr.pairs.toString());
        }
        if(tr.equationsSet!=null) {
            System.err.println("EQUATIONS:");
            System.err.println(tr.equationsSet.toString());
        }
        if(tr.qFunctionApplicationSet!=null) {
            System.err.println("Q:");
            System.err.println(tr.qFunctionApplicationSet.toString());
        }
    }
*/
}
