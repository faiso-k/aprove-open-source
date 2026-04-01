package aprove.input.Programs.srs;

import java.io.*;
import java.util.*;

import aprove.*;
import aprove.input.Generated.srs.lexer.*;
import aprove.input.Generated.srs.node.*;
import aprove.input.Generated.srs.parser.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** ProgramTranslator for translating SRS programs into internal representation.
 * @author Peter Schneider-Kamp, Stephan Falke
 * @version $Id$
 */

public class Translator extends ProgramTranslator {

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
        pe.setMessage(e.getMessage().replaceFirst("\\0133[0-9]+,[0-9]+\\0135\\s",""));
        if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
            e.printStackTrace();
        }
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

    Pass1 p1 = new Pass1();
    p1.setProgram(this.program);
    p1.setErrors(this.getErrors());
    tree.apply(p1);

    Pass2 p2 = new Pass2();
    p2.setProgram(p1.getProgram());
    p2.setErrors(this.getErrors());
    tree.apply(p2);

    this.program = p2.getProgram();
    }

    private static Program predefine(Program prog) {
    try {
        // polymorph sort
        Sort poly = Sort.create(Sort.standardName, new Vector<ConstructorSymbol>());
        prog.addSort(poly);
    } catch (ProgramException e) {
        throw new RuntimeException("Internal error building predefined symbols for SRS");
    }
    prog.setStrategy(Program.ALL);
    prog.setComplete(true);
    return prog;
    }

    @Override
    public Language getLanguage() {
        return Language.SES;
    }

}
