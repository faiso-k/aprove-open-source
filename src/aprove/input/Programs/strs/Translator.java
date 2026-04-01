package aprove.input.Programs.strs;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.input.Generated.strs.lexer.*;
import aprove.input.Generated.strs.node.*;
import aprove.input.Generated.strs.parser.*;
import aprove.input.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.ConditionalRewriting.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.LinearArithmetic.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TheoremProver.*;
import aprove.verification.theoremprover.TheoremProverProcedures.Induction.*;

/**
 * Translator for translating sorted (C)TRSs into internal representation.
 *
 * @author dickmeis
 * @version $Id$
 */

public class Translator extends ProgramTranslator {

    protected List<Formula> extractedFormulas;

    protected static Logger logger =
            Logger.getLogger("aprove.input.Programs.strs.Translator");

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

        // GetTokenClasses.getTokens(reader, tokens, this.errors);
        if (this.getErrors().getMaxLevel() >= ParseError.ERROR) {
            this.program = null;
            return;
        }

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

        try {
            Lexer lexer = new Lexer(new PushbackReader(reader, 1024));
            Parser parser = new Parser(lexer);
            tree = parser.parse();
        }
        catch (Exception e) {
            ParseError pe = new ParseError(ParseError.ERROR);
            if (e instanceof ParserException) {
                Token t = ((ParserException) e).getToken();
                pe.setToken(t.toString().trim());
                pe.setPosition(t.getLine(), t.getPos());
            }
            pe.setMessage(e.getMessage().replaceFirst(
                    "\\0133[0-9]+,[0-9]+\\0135\\s", ""));
            this.getErrors().add(pe);
            this.program = null;
            return;
        }

        try {
            this.translate(tree);

            reader = new StringReader(inputCommentLineAnalyser.toString());

            CommentLineAnalyzer commentLineAnalyzer = new CommentLineAnalyzer(
                    reader, "#", "", this.getProgram());

            this.extractedFormulas = commentLineAnalyzer.checkForFormulas();
        }
        catch (Exception e) {
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

        PrePass prepass = new PrePass();
        tree.apply(prepass);
        this.getErrors().addAll(prepass.getErrors());

        Stack<String> definedFunctSymb = prepass.getDefinedFunctSymb();

        FullPass fullpass = new FullPass(definedFunctSymb);

        tree.apply(fullpass);
        this.getErrors().addAll(fullpass.getErrors());

        if (this.getErrors().isEmpty()){
            this.program = fullpass.getProgram();
        } else {
            this.program = null;
        }

        this.checkExistence0AryConstructors();

        // check which def function symbol is (semi) LA based
        Set<DefFunctionSymbol> functionSymbols = this.program.getDefFunctionSymbols();
        for (DefFunctionSymbol functionSymbol : functionSymbols) {
            CoverSet cst = CoverSet.createCoverSet(functionSymbol, new HashSet<AlgebraVariable>(), this.program);
            if(cst.isLABased()){
                this.program.laProgramProperties.laBasedFunctionSymbols.add(functionSymbol);
                this.program.laProgramProperties.semilaBasedFunctionSymbols.add(functionSymbol);
                if(!this.isLAMatcherUnique(cst)){
                    ParseError pe = new ParseError();
                    pe.setMessage("LA matcher not guarenteed to be unique");
                    this.getErrors().add(pe);
                }

                boolean laComplete = cst.isLAComplete();
                if(!laComplete){
                    ParseError pe = new ParseError();
                    pe.setMessage("The la based function symbol " + functionSymbol + " has not got a complete definition.");
                    this.getErrors().add(pe);
                    System.err.println("The la based function symbol " + functionSymbol + " has not got a complete definition.");
                }
            }
            else if(cst.isSemiLABased()){
                this.program.laProgramProperties.semilaBasedFunctionSymbols.add(functionSymbol);
                if(!this.isLAMatcherUnique(cst)){
                    ParseError pe = new ParseError();
                    pe.setMessage("LA matcher not guarenteed to be unique");
                    this.getErrors().add(pe);
                }

                boolean laComplete = cst.isLAComplete();
                if(!laComplete){
                    ParseError pe = new ParseError();
                    pe.setMessage("The la based function symbol " + functionSymbol + " has not got a complete definition.");
                    this.getErrors().add(pe);
                    System.err.println("The la based function symbol " + functionSymbol + " has not got a complete definition.");
                }
            }
            else if(cst.usesLA()){
              ParseError pe = new ParseError();
              pe.setMessage("forbidden use of LA in a not semi LA based definition");
              this.getErrors().add(pe);
            }
            else{
                boolean complete = cst.isComplete(this.program);
                if(!complete){
                    ParseError pe = new ParseError();
                    pe.setMessage("The function symbol " + functionSymbol + " has possible not got a complete definition.");
                    this.getErrors().add(pe);
                    System.err.println("The function symbol " + functionSymbol + " has possible not got a complete definition.");
                }
            }
        }


        ConditionalCriticalPairs ccps = ConditionalCriticalPairs.create(this.program);
        ccps.removeJoinable(this.program);

        if(!ccps.isEmpty()){
            ParseError pe = new ParseError();
            pe.setMessage("maybe not confluent");
            this.getErrors().add(pe);
            if(Globals.DEBUG_DICKMEIS){
                System.err.println("maybe not confluent");
                System.err.println(ccps);
            }
        }

        if(!this.getErrors().isEmpty()){
            this.program = null;
        }

    }

    /**
     * checks if for every sort there is a constant = a 0-ary constructor
     */
    private void checkExistence0AryConstructors() {
        Set<Sort> sorts = this.program.getSorts();
        outer : for (Sort sort : sorts) {
            List<ConstructorSymbol> css = sort.getConstructorSymbols();
            for (ConstructorSymbol symbol : css) {
                int arity = symbol.getArity();
                if(arity==0){
                    continue outer;
                }
            }

            ParseError pe = new ParseError();
            pe.setMessage("Sort " + sort + " has not got any 0 ary constructor");
            this.getErrors().add(pe);
        }

    }

    private boolean isLAMatcherUnique(CoverSet coverSet){
        for (CoverSetTriple cst : coverSet.getCoverSetTriples()) {

            Set<AlgebraVariable> cstVars = cst.getVariables();

            LinearIntegerConstraintSimplifier lics = new LinearIntegerConstraintSimplifier(cstVars);

            FreshVarGenerator fvg = new FreshVarGenerator(cstVars);

            List<AlgebraTerm> args = cst.getLeftArguments();
            for (AlgebraTerm term : args) {

                AlgebraVariable fvar = fvg.getFreshVariable("u", this.program.laProgramProperties.sortNat, false);

                LinearConstraint constraint = LinearConstraint.createEquation(term, fvar, this.program.laProgramProperties);

                if(constraint == null){
                    return false;
                }
                else{
                    lics.addConstraint(constraint);
                }

            }

            boolean invertable = lics.isInvertable(cstVars);
            if(!invertable){
                return false;
            }
        }

        return true;
    }

    @Override
    public Object getState()  {
        return new ProgramContainingFormulas(this.getProgram(), this.extractedFormulas);
    }

    @Override
    public Language getLanguage() {
        return Language.STRS;
    }

}
