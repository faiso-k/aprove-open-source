package aprove.input.Programs.fp;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.input.Generated.fp.node.*;
import aprove.input.Generated.fp.parser.*;
import aprove.input.*;
import aprove.input.Programs.Predef.IntegerPredef.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Programs.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.theoremprover.TheoremProver.*;

/**
 * ProgramTranslator for translating FP programs into internal representation.
 * @author Peter Schneider-Kamp, Christian Haselbach
 * @version $Id$
 */
public class Translator extends ProgramTranslator {

    protected List<Formula> extractedFormulas;

    protected static Logger logger = Logger.getLogger("aprove.input.Programs.fp.Translator");

    @Override
    public void translate(Reader reader) throws TranslationException {

        int read;
        char[] buffer = new char[4096];
        StringBuffer inputParser = new StringBuffer();
        StringBuffer inputCommentLineAnalyser = new StringBuffer();

        try {
            while ((read = reader.read(buffer)) != -1) {
                inputParser.append(buffer, 0, read);
                inputCommentLineAnalyser.append(buffer, 0, read);
            }
        } catch (IOException e) {
            throw new TranslationException(e);
        }

        // make the input always end with a newline
        if (!inputParser.toString().endsWith("\n")) {
            inputParser.append("\n");
        }

        reader = new StringReader(inputParser.toString());

        Set<String> tokens = new HashSet<String>();
        GetTokenClasses.getTokens(reader, tokens, this.getErrors());
        if (this.getErrors().getMaxLevel() >= ParseError.ERROR) {
            this.program = null;
            return;
        }

        tokens.add("bool");
        tokens.add("then");
        tokens.add("else");
        tokens.add("and");
        tokens.add("or");
        tokens.add("not");
        tokens.add("isa_true");
        tokens.add("isa_false");
        tokens.add("infix");
        tokens.add("infixr");
        tokens.add("infixl");
        tokens.add("isa");

        // adding the data structure symbol for integers and the constructors and selectors
        tokens.add("int");
        tokens.addAll(IntegerTools.getIntegerDataStructureTokens());

        try {
            reader.reset();
        } catch (IOException e) {
            throw new TranslationException(e);
        }
        Start tree;
        if (this.program == null) {
            this.program = Program.create();
            this.program.setTypeContext(new TypeContext());
        }
        if (this.program.getSort("bool") == null) {
            this.program = Translator.predefine(this.program);
        }
        try {
            tree = new Parser(new FPLexer(new PushbackReader(reader, 10240), tokens)).parse();
        } catch (Exception e) {
            ParseError pe = new ParseError(ParseError.ERROR);
            if (e instanceof ParserException) {
                Token t = ((ParserException) e).getToken();
                pe.setToken(t.toString().trim());
                pe.setPosition(t.getLine(), t.getPos());
            }
            pe.setMessage(e.getMessage().replaceFirst("\\0133[0-9]+,[0-9]+\\0135\\s", ""));
            this.getErrors().add(pe);
            this.program = null;
            return;
        }

        try {
            this.translate(tree);

            reader = new StringReader(inputCommentLineAnalyser.toString());

            CommentLineAnalyzer commentLineAnalyzer = new CommentLineAnalyzer(reader,
                                                                              "#",
                                                                              "formula:",
                                                                              this.getProgram());

            this.extractedFormulas = commentLineAnalyzer.checkForFormulas();

        } catch (Exception e) {
            ParseError pe = new ParseError(ParseError.ERROR);
            if (e instanceof ParserException) {
                Token t = ((ParserException) e).getToken();
                pe.setToken(t.toString().trim());
            }
            pe.setMessage(e.getMessage());
            if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                e.printStackTrace();
            }
            this.getErrors().add(pe);
        }

    }

    private void translate(Start tree) {
        Hashtable<String, TId> sorttoken = new Hashtable<String, TId>();
        sorttoken.put("bool", new TId("bool"));

        PredefPass predefPass = new PredefPass();
        predefPass.setSorttoken(sorttoken);
        predefPass.setErrors(this.getErrors());
        predefPass.setProgram(this.program);
        predefPass.setUsedNames(new HashSet<String>());
        predefPass.setTypeContext(this.program.getTypeContext());
        tree.apply(predefPass);

        Pass pConstFuncPass = new ConstFuncPass();
        pConstFuncPass.set(predefPass);
        tree.apply(pConstFuncPass);

        Pass tp = new TransformPass();
        tp.set(pConstFuncPass);
        tree.apply(tp);

        Pass pRenameConstFuncPass = new RenameConstFuncPass();
        pRenameConstFuncPass.set(tp);
        tree.apply(pRenameConstFuncPass);

        Pass1 p1 = new Pass1();
        p1.set(pRenameConstFuncPass);
        tree.apply(p1);

        Pass2 p2 = new Pass2();
        p2.set(p1);
        tree.apply(p2);
        if (this.getErrors().getMaxLevel() >= ParseError.ERROR) {
            this.program = null;
            return;
        }

        //    TransformPass tp = new TransformPass();
        //    tp.set(p2);
        //    tree.apply(tp);

        Pass3 p3 = new Pass3();
        p3.set(p2);
        tree.apply(p3);
        this.program = p3.getProgram();
        if (this.getErrors().getMaxLevel() >= ParseError.ERROR) {
            this.program = null;
        }
        if (this.program != null && this.program.getTypeContext() != null) {
            Translator.logger.log(Level.FINE, "Type context:\n" + this.program.getTypeContext().toString());
        }
        //    System.err.println(program.getTypeContext().toString());
    }

    /**
     * Note the *hard-coded String literals* in the method body.
     * These "special" Strings occur quite a few times as String literals
     * (as opposed to: references to a constant) scattered over AProVE.
     * So if you intend to generalize from these Strings ("bool", "true",
     * ...), be warned that this is not just a local change. It may be more
     * convenient to just rename the symbols that the user supplied as an
     * input to something that does not clash with these literals.
     */
    public static Program predefine(Program prog) {
        TypeContext typeContext = new TypeContext();
        prog.setTypeContext(typeContext);
        prog.setSimplifiable(true);
        prog.setStrategy(Program.INNERMOST);
        try {
            TypeDefinition curTypeDef = new TypeDefinition(TypeTools.getTypeCons("bool", 0));
            typeContext.addTypeDef(curTypeDef);

            AlgebraTerm BoolCon = curTypeDef.getDefTerm();
            Type bTyp = TypeTools.autoQuan(BoolCon);
            List<AlgebraTerm> lot = new Vector<AlgebraTerm>();
            lot.add(BoolCon);
            Type b_bTyp = TypeTools.autoQuan(TypeTools.function(lot, curTypeDef.getDefTerm()));

            lot = new Vector<AlgebraTerm>();
            lot.add(BoolCon);
            lot.add(BoolCon);
            Type bb_bTyp = TypeTools.autoQuan(TypeTools.function(lot, curTypeDef.getDefTerm()));

            Predefined pd = prog.getPredefined();
            // bool
            Sort bool = Sort.create("bool", new Vector<ConstructorSymbol>());
            pd.setBool(bool);
            ConstructorSymbol ctrue = ConstructorSymbol.create("true", new Vector<Sort>(), bool);
            curTypeDef.setSingleTypeOf(ctrue, bTyp);
            pd.setTrue(ctrue);
            bool.addConstructorSymbol(ctrue);
            prog.addConstructorSymbol(ctrue);
            ConstructorSymbol cfalse = ConstructorSymbol.create("false", new Vector<Sort>(), bool);
            curTypeDef.setSingleTypeOf(cfalse, bTyp);
            pd.setFalse(cfalse);
            bool.addConstructorSymbol(cfalse);
            prog.addConstructorSymbol(cfalse);
            prog.addSort(bool);
            AlgebraTerm ttrue = ConstructorApp.create(ctrue);
            AlgebraTerm tfalse = ConstructorApp.create(cfalse);
            ctrue.setSelectors(new Vector<DefFunctionSymbol>());
            cfalse.setSelectors(new Vector<DefFunctionSymbol>());
            // equal_bool
            DefFunctionSymbol feq = DefFunctionSymbol.create(new String("equal_bool"), new Vector<Sort>(), bool);
            typeContext.setSingleTypeOf(feq, bb_bTyp);
            bool.setEqualOp(feq);
            feq.setTermination(true); // by construction
            feq.addArgSort(bool);
            feq.addArgSort(bool);
            AlgebraTerm args2[] = { ttrue, tfalse };
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
            DefFunctionSymbol fand = DefFunctionSymbol.create(new String("and"), new Vector<Sort>(), bool);
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
            DefFunctionSymbol f_or = DefFunctionSymbol.create(new String("or"), new Vector<Sort>(), bool);
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
            DefFunctionSymbol fnot = DefFunctionSymbol.create(new String("not"), new Vector<Sort>(), bool);
            typeContext.setSingleTypeOf(fnot, b_bTyp);
            pd.setNot(fnot);
            fnot.setTermination(true); // by construction
            fnot.addArgSort(bool);
            prog.addPredefFunctionSymbol(fnot);
            fnot.setSignatureClass(Symbol.BOOLSIG);
            AlgebraTerm args1[] = { tfalse };
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
        } catch (ProgramException e) {
            throw new RuntimeException("Internal error building predefined symbols for FP");
        }
        return prog;
    }

    @Override
    public Object getState() {
        return new ProgramContainingFormulas(this.getProgram(), this.extractedFormulas);
    }

    @Override
    public Language getLanguage() {
        return Language.FP;
    }

}
