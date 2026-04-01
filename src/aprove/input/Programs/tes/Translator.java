package aprove.input.Programs.tes;

import java.io.*;
import java.util.*;
import java.util.regex.*;

import aprove.input.Generated.tes.lexer.*;
import aprove.input.Generated.tes.node.*;
import aprove.input.Generated.tes.parser.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** ProgramTranslator for translating TES programs into internal representation.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public class Translator extends ProgramTranslator {

    Language language = null;

    @Override
    public void translate(Reader reader) {
        try {
            this.translate(new Parser(new Lexer(new PushbackReader(reader, 10240))).parse());
        }
        catch (Exception e) {
            ParseError pe = new ParseError(ParseError.ERROR);
            if (e instanceof ParserException) {
                Token t = ((ParserException)e).getToken();
                pe.setToken(t.toString().trim());
                pe.setPosition(t.getLine(), t.getPos());
            }
            else if (e instanceof LexerException) {
                try {
                    Matcher m = Pattern.compile(".*\\0133([0-9]+),([0-9]+)\\0135\\s.*").matcher(e.getMessage());
                    m.matches();
                    pe.setPosition(Integer.parseInt(m.group(1)), Integer.parseInt(m.group(2)));
                }
                catch (Exception e1) { System.err.println(e1.getMessage()); }
            }
            pe.setMessage(e.getMessage().replaceFirst("\\0133[0-9]+,[0-9]+\\0135\\s",""));
            this.getErrors().add(pe);
        }
        if (this.getErrors().getMaxLevel() >= ParseError.ERROR) {
            this.program = null;
        }
    }

    protected void translate(Start tree) {
        if (this.program == null) {
            this.program = Translator.predefine(Program.create());
        }

        Pass0 p0 = new Pass0();
        p0.setProgram(this.program);
        p0.setVars(new HashSet());
        p0.setErrors(this.getErrors());
        tree.apply(p0);

        Pass1 p1 = new Pass1();
        p1.setProgram(p0.getProgram());
        p1.setVars(p0.getVars());
        p1.setErrors(this.getErrors());
        tree.apply(p1);

        Pass2 p2 = new Pass2();
        p2.setProgram(p1.getProgram());
        p2.setVars(p1.getVars());
        p2.setErrors(this.getErrors());
        tree.apply(p2);

        Pass3 p3 = new Pass3();
        p3.setProgram(p2.getProgram());
        p3.setVars(p2.getVars());
        p3.setErrors(this.getErrors());
        tree.apply(p3);

        this.program = p3.getProgram();

        if (this.program.isEquational()) {
            this.language = Language.ETES;
        } else {
            this.language = Language.TES;
        }
    }

    private static Program predefine(Program prog) {
        try {
            // polymorph sort
            Sort poly = Sort.create(Sort.standardName, new Vector<ConstructorSymbol>());
            prog.addSort(poly);
        } catch (ProgramException e) {
            throw new RuntimeException("Internal error building predefined symbols for TES");
        }
        prog.setStrategy(Program.ALL);
        prog.setComplete(true);
        return prog;
    }

    @Override
    public Language getLanguage() {
        return this.language;
    }

}
