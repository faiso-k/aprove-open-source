package aprove.input.Programs.idp;

import java.io.*;
import java.util.*;

import aprove.input.Generated.idp.lexer.*;
import aprove.input.Generated.idp.node.*;
import aprove.input.Generated.idp.parser.*;
import aprove.input.Programs.idp.IDPProblemPass.*;
import aprove.input.Utility.*;
import aprove.verification.complexity.CpxITrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Input.*;
import immutables.*;

/**
 * Translator class to parse IDP problems.
 *
 * @author noschinski
 * @version $Id$
 */
public class Translator extends aprove.verification.oldframework.Input.Translator.TranslatorSkeleton {

    /**
     * Decides whether the Translator acts as IDP or ITRS parser.
     *
     * <ul>
     * <li>In IDP mode, the parser does not accept conditional rules (as their
     * transformation into unconditional rules would alter Dependency Pairs.</li>
     * <li>In ITRS mode, the parser does not accept PAIRS sections.</li>
     * </ul>
     */
    final ParserLanguage mode;

    /**
     * Generates a new Translator in IDP mode
     */
    public Translator() {
        this(ParserLanguage.IDP);
    }

    public Translator(final ParserLanguage mode) {
        super();
        this.mode = mode;
    }

    private Language language = null;

    @Override
    public Language getLanguage() {
        if (this.language == null) {
            throw new RuntimeException("getLanguage called before language was determined");
        }
        return this.language;
    }

    @Override
    public void translate(final Reader reader) throws TranslationException {
        Lexer lexer = new Lexer(new PushbackReader(reader, 1024));
        Parser parser = new Parser(lexer);
        try {
            Start tree = parser.parse();
            this.translate(tree);
        } catch (LexerException e) {
            ParseError pe = new ParseError(ParseError.ERROR);
            pe.setMessage("Lexer exception: " + e.getMessage());
            this.getErrors().add(pe);
        } catch (ParserException e) {
            ParseError pe = new ParseError(ParseError.ERROR);
            Token t = e.getToken();
            pe.setToken(t.toString().trim());
            pe.setPosition(t.getLine(), t.getPos());
            pe.setMessage("Parser: " + e.getMessage());
            this.getErrors().add(pe);
        } catch (IOException e) {
            throw new TranslationException(e);
        }
    }

    protected void translate(final Start tree) throws TranslationException {
        final CollectVarsPass vPass = new CollectVarsPass();
        tree.apply(vPass);
        final Set<String> vars = vPass.getVariables();

        final IDPProblemPass idpPass = new IDPProblemPass(this.mode, vars);
        tree.apply(idpPass);

        this.getErrors().addAll(idpPass.getErrors());

        /*
         * If we are analyzing a cint and an explicit analysis goal is missing,
         * then we force complexity analysis of the symbol that was given as
         * proto-annotation, if any.
         */
        boolean forceComplexity = false;
        if (this.mode == ParserLanguage.CINT) {
            forceComplexity = !idpPass.complexityGoal && this.getProtoAnnotation() != null && !this.getProtoAnnotation().isEmpty();
        }

        boolean analyzeComplexity = idpPass.complexityGoal || forceComplexity;
        StartTermType startTermType = forceComplexity ? StartTermType.FunctionSymbols : idpPass.startterm;

        if (startTermType == StartTermType.Full && !analyzeComplexity) {
            if (this.mode == ParserLanguage.IDP) {
                this.setState(idpPass.getIDPProblem());
                this.language = Language.IDP;
            } else {
                this.setState(ITRSProblem.create(idpPass.getRAnalysis(), idpPass.getQ()));
                this.language = Language.ITRS;
            }
        } else if (
            (startTermType == StartTermType.ConstructorBased || startTermType == StartTermType.FunctionSymbols)
            && analyzeComplexity
            && this.mode == ParserLanguage.CINT)
        {
            try {
                Set<IGeneralizedRule> rules = idpPass.getRRules();
                LinkedHashSet<CpxIntTupleRule> itrules = new LinkedHashSet<>();
                for (IGeneralizedRule r : rules) {
                    itrules.addAll(CpxIntTupleRule.createRules(r));
                }
                LinkedHashSet<FunctionSymbol> lhsSyms = new LinkedHashSet<>();
                for (CpxIntTupleRule rule : itrules) {
                    lhsSyms.add(rule.getRootSymbol());
                }
                LinkedHashSet<FunctionSymbol> startSymbols = new LinkedHashSet<>();
                if (startTermType == StartTermType.FunctionSymbols) {
                    Collection<String> symNames = forceComplexity ? Collections.singleton(this.getProtoAnnotation()) : idpPass.getStartsymbols();
                    for (String symName : symNames) {
                        for (FunctionSymbol sym : lhsSyms) {
                            if (sym.getName().equals(symName)) {
                                startSymbols.add(sym);
                            }
                        }
                    }
                } else {
                    startSymbols.addAll(lhsSyms);
                }
                this.setState(
                    CpxIntTrsProblem.create(ImmutableCreator.create(itrules), ImmutableCreator.create(startSymbols))
                );
                this.language = Language.CpxIntTrs;
            } catch (Exception e) {
                throw new TranslationException(e);
            }
        } else if (startTermType == StartTermType.ConstructorBased
            && analyzeComplexity
            && this.mode == ParserLanguage.ITRS)
        {
            this.setState(CpxITrsProblem.create(idpPass.getRAnalysis(), idpPass.getQ()));
            this.language = Language.CpxITrs;
        } else {
            throw new TranslationException("Problemtype "
                + this.mode.toString()
                + ", startterm: "
                + startTermType.toString()
                + (analyzeComplexity ? ", complexity" : "")
                + " not supported");
        }
    }

}
