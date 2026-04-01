package aprove.input.Programs.ttt;

import java.io.*;
import java.util.*;

import aprove.input.Generated.ttt.lexer.*;
import aprove.input.Generated.ttt.node.*;
import aprove.input.Generated.ttt.parser.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** ProgramTranslator for translating TES programs into internal representation.
 * @author Peter Schneider-Kamp
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
        p0.initVars(tree);
        p0.initInfixes(tree);
        p0.setErrors(this.getErrors());
        tree.apply(p0);

        Pass1 p1 = new Pass1();
        p1.setProgram(p0.getProgram());
        p1.setVars(p0.getVars());
        p1.setInfixes(p0.getInfixes());
        p1.setErrors(this.getErrors());
        tree.apply(p1);

        Pass2 p2 = new Pass2();
        p2.setProgram(p1.getProgram());
        p2.setVars(p1.getVars());
        p2.setInfixes(p1.getInfixes());
        p2.setErrors(this.getErrors());
        tree.apply(p2);

        Pass3 p3 = new Pass3();
        p3.setProgram(p2.getProgram());
        p3.setVars(p2.getVars());
        p3.setInfixes(p2.getInfixes());
        p3.setErrors(this.getErrors());
        tree.apply(p3);

        this.program = p3.getProgram();
    }

    private static Program predefine(Program prog) {
        try {
            // polymorph sort
            Sort poly = Sort.create(Sort.standardName, new Vector<ConstructorSymbol>());
            prog.addSort(poly);
        } catch (ProgramException e) {
            throw new RuntimeException("Internal error building predefined symbols for TTT");
        }
        prog.setStrategy(Program.ALL);
        prog.setComplete(true);
        return prog;
    }

    @Override
    public Language getLanguage() {
        return Language.TES;
    }

}
