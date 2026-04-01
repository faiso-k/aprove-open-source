package aprove.input.Programs.ipad;

import java.io.*;
import java.util.*;
import java.util.logging.*;
import java.util.regex.*;

import aprove.*;
import aprove.input.Generated.ipad.lexer.*;
import aprove.input.Generated.ipad.node.*;
import aprove.input.Generated.ipad.parser.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Programs.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

/** Translator class for the language ipad.
 *  @author Christian Haselbach
 *  @version $Id$
 */

public class Translator extends ProgramTranslator {
    protected static Logger logger = Logger.getLogger("aprove.input.Programs.ipad.Translator");

    @Override
    public void translate(final Reader reader) {
        Start tree = null;
        try {
            tree = new Parser(new Lexer(new PushbackReader(reader, 10240))).parse();
        } catch (final Exception e) {
            final ParseError pe = new ParseError(ParseError.ERROR);
            if (e instanceof ParserException) {
                final Token t = ((ParserException) e).getToken();
                pe.setToken(t.toString().trim());
                pe.setPosition(t.getLine(), t.getPos());
            } else if (e instanceof LexerException) {
                try {
                    final Matcher m = Pattern.compile(".*\\0133([0-9]+),([0-9]+)\\0135\\s.*").matcher(e.getMessage());
                    m.matches();
                    pe.setPosition(Integer.parseInt(m.group(1)), Integer.parseInt(m.group(2)));
                } catch (final Exception e1) {
                    System.err.println(e1.getMessage());
                }
            }
            pe.setMessage(e.getMessage().replaceFirst("\\0133[0-9]+,[0-9]+\\0135\\s", ""));
            this.getErrors().add(pe);
            return;
        }
        try {
            this.translate(tree);
        } catch (final Exception e) {
            final ParseError pe = new ParseError(ParseError.ERROR);
            pe.setMessage(e.getMessage());
            if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                e.printStackTrace();
            }
            this.getErrors().add(pe);
        }
        if (this.getErrors().getMaxLevel() >= ParseError.ERROR) {
            this.program = null;
        }
    }

    protected void translate(final Start tree) {
        if (this.program == null) {
            this.program = Program.create();
            this.program.setTypeContext(new TypeContext());
        }
        if (this.program.getSort("bool") == null) {
            this.program = Translator.predefine(this.program);
        }
        Pass pass = new PredefStructPass();
        pass.setProgram(this.program);
        pass.setErrors(this.getErrors());
        pass.setProcHeads(new Hashtable());
        pass.setTypeContext(this.program.getTypeContext());
        pass.setSorttoken(new Hashtable());

        tree.apply(pass);

        pass = (new StructPass()).set(pass);
        tree.apply(pass);
        pass = (new SymbPass()).set(pass);
        tree.apply(pass);
        pass = (new WitnessPass()).set(pass);
        tree.apply(pass);
        pass = (new SugarPass()).set(pass);
        tree.apply(pass);
        pass = (new IntegerPredefOperatorPrecedencePass()).set(pass);
        tree.apply(pass);
        pass = (new TransformPass()).set(pass);
        tree.apply(pass);
        pass = (new StatementPass()).set(pass);
        tree.apply(pass);
        this.program = pass.getProgram();
        Translator.logger.log(Level.FINE, "Type context:\n" + pass.getTypeContext().toString());

        //System.err.println(this.program.toString());
        //System.err.println((pass.getTypeContext()).toString());
    }

    private static Program predefine(final Program prog) {
        final TypeContext typeContext = new TypeContext();
        prog.setSimplifiable(true);
        prog.setStrategy(Program.INNERMOST);
        try {
            final TypeDefinition curTypeDef = new TypeDefinition(TypeTools.getTypeCons("bool", 0));
            typeContext.addTypeDef(curTypeDef);

            final AlgebraTerm BoolCon = curTypeDef.getDefTerm();
            final Type bTyp = TypeTools.autoQuan(BoolCon);
            List<AlgebraTerm> lot = new Vector<AlgebraTerm>();
            lot.add(BoolCon);
            final Type b_bTyp = TypeTools.autoQuan(TypeTools.function(lot, curTypeDef.getDefTerm()));

            lot = new Vector<AlgebraTerm>();
            lot.add(BoolCon);
            lot.add(BoolCon);
            final Type bb_bTyp = TypeTools.autoQuan(TypeTools.function(lot, curTypeDef.getDefTerm()));

            final Predefined pd = prog.getPredefined();
            // bool
            final Sort bool = Sort.create("bool", new Vector<ConstructorSymbol>());
            pd.setBool(bool);
            final ConstructorSymbol ctrue = ConstructorSymbol.create("true", new Vector<Sort>(), bool);
            curTypeDef.setSingleTypeOf(ctrue, bTyp);
            pd.setTrue(ctrue);
            bool.addConstructorSymbol(ctrue);
            prog.addConstructorSymbol(ctrue);
            final ConstructorSymbol cfalse = ConstructorSymbol.create("false", new Vector<Sort>(), bool);
            curTypeDef.setSingleTypeOf(cfalse, bTyp);
            pd.setFalse(cfalse);
            bool.addConstructorSymbol(cfalse);
            prog.addConstructorSymbol(cfalse);
            prog.addSort(bool);
            final AlgebraTerm ttrue = ConstructorApp.create(ctrue);
            final AlgebraTerm tfalse = ConstructorApp.create(cfalse);
            ctrue.setSelectors(new Vector<DefFunctionSymbol>());
            cfalse.setSelectors(new Vector<DefFunctionSymbol>());
            // equal_bool
            final DefFunctionSymbol feq = DefFunctionSymbol.create(new String("equal_bool"), new Vector<Sort>(), bool);
            typeContext.setSingleTypeOf(feq, bb_bTyp);
            bool.setEqualOp(feq);
            feq.setTermination(true); // by construction
            feq.addArgSort(bool);
            feq.addArgSort(bool);
            final AlgebraTerm args2[] = {ttrue, tfalse };
            AlgebraTerm l = DefFunctionApp.create(feq, args2);
            prog.addRule(feq, Rule.create(l, tfalse));
            args2[0] = tfalse;
            args2[1] = ttrue;
            l = DefFunctionApp.create(feq, args2);
            prog.addRule(feq, Rule.create(l, tfalse));
            args2[0] = ttrue;
            l = DefFunctionApp.create(feq, args2);
            prog.addRule(feq, Rule.create(l, ttrue));
            args2[0] = tfalse;
            args2[1] = tfalse;
            l = DefFunctionApp.create(feq, args2);
            prog.addRule(feq, Rule.create(l, ttrue));
            prog.addPredefFunctionSymbol(feq);
            feq.setSignatureClass(Symbol.BOOLSIG);
            // and
            final DefFunctionSymbol fand = DefFunctionSymbol.create(new String("and"), new Vector<Sort>(), bool);
            typeContext.setSingleTypeOf(fand, bb_bTyp);
            pd.setAnd(fand);
            fand.setTermination(true); // by construction
            fand.addArgSort(bool);
            fand.addArgSort(bool);
            fand.setFixity(SyntacticFunctionSymbol.INFIXR);
            fand.setFixityLevel(3);
            AlgebraTerm x = AlgebraVariable.create(VariableSymbol.create("x", bool));
            args2[0] = ttrue;
            args2[1] = x;
            l = DefFunctionApp.create(fand, args2);
            prog.addRule(fand, Rule.create(l, x));
            x = AlgebraVariable.create(VariableSymbol.create("x", bool));
            args2[0] = tfalse;
            args2[1] = x;
            l = DefFunctionApp.create(fand, args2);
            prog.addRule(fand, Rule.create(l, tfalse));
            prog.addPredefFunctionSymbol(fand);
            fand.setSignatureClass(Symbol.BOOLSIG);
            // or
            final DefFunctionSymbol f_or = DefFunctionSymbol.create(new String("or"), new Vector<Sort>(), bool);
            typeContext.setSingleTypeOf(f_or, bb_bTyp);
            pd.setOr(f_or);
            f_or.setTermination(true); // by construction
            f_or.addArgSort(bool);
            f_or.addArgSort(bool);
            f_or.setFixity(SyntacticFunctionSymbol.INFIXR);
            f_or.setFixityLevel(2);
            x = AlgebraVariable.create(VariableSymbol.create("x", bool));
            args2[0] = ttrue;
            args2[1] = x;
            l = DefFunctionApp.create(f_or, args2);
            prog.addRule(f_or, Rule.create(l, ttrue));
            x = AlgebraVariable.create(VariableSymbol.create("x", bool));
            args2[0] = tfalse;
            args2[1] = x;
            l = DefFunctionApp.create(f_or, args2);
            prog.addRule(f_or, Rule.create(l, x));
            prog.addPredefFunctionSymbol(f_or);
            f_or.setSignatureClass(Symbol.BOOLSIG);
            // not
            final DefFunctionSymbol fnot = DefFunctionSymbol.create(new String("not"), new Vector<Sort>(), bool);
            typeContext.setSingleTypeOf(fnot, b_bTyp);
            pd.setNot(fnot);
            fnot.setTermination(true); // by construction
            fnot.addArgSort(bool);
            prog.addPredefFunctionSymbol(fnot);
            fnot.setSignatureClass(Symbol.BOOLSIG);
            final AlgebraTerm args1[] = {tfalse };
            prog.addRule(fnot, Rule.create(DefFunctionApp.create(fnot, args1), ttrue));
            args1[0] = ttrue;
            prog.addRule(fnot, Rule.create(DefFunctionApp.create(fnot, args1), tfalse));
            // isa_true
            DefFunctionSymbol fisa = DefFunctionSymbol.create(new String("isa_true"), new Vector<Sort>(), bool);
            typeContext.setSingleTypeOf(fisa, b_bTyp);
            ctrue.setIsa(fisa);
            fisa.setTermination(true); // by construction
            fisa.addArgSort(bool);
            prog.addPredefFunctionSymbol(fisa);
            fisa.setSignatureClass(Symbol.BOOLSIG);
            args1[0] = ttrue;
            prog.addRule(fisa, Rule.create(DefFunctionApp.create(fisa, args1), ttrue));
            args1[0] = tfalse;
            prog.addRule(fisa, Rule.create(DefFunctionApp.create(fisa, args1), tfalse));
            // isa_false
            fisa = DefFunctionSymbol.create(new String("isa_false"), new Vector<Sort>(), bool);
            typeContext.setSingleTypeOf(fisa, b_bTyp);
            cfalse.setIsa(fisa);
            fisa.setTermination(true); // by construction
            fisa.addArgSort(bool);
            prog.addPredefFunctionSymbol(fisa);
            fisa.setSignatureClass(Symbol.BOOLSIG);
            args1[0] = ttrue;
            prog.addRule(fisa, Rule.create(DefFunctionApp.create(fisa, args1), tfalse));
            args1[0] = tfalse;
            prog.addRule(fisa, Rule.create(DefFunctionApp.create(fisa, args1), ttrue));
        } catch (final ProgramException e) {
            throw new RuntimeException("Internal error building predefined symbols for FP");
        }
        prog.setTypeContext(typeContext);
        return prog;
    }

    @Override
    public Language getLanguage() {
        return Language.IPAD;
    }
}
