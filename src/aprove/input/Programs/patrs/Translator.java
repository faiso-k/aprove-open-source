package aprove.input.Programs.patrs;

import java.io.*;
import java.util.*;

import aprove.input.Generated.patrs.lexer.*;
import aprove.input.Generated.patrs.node.*;
import aprove.input.Generated.patrs.parser.*;
import aprove.input.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.PATRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Input.*;
import immutables.*;

/**
 * Translator class to parse PATRS problems.
 *
 * @author Stephan Falke
 * @version $Id$
 */
public class Translator extends aprove.verification.oldframework.Input.Translator.TranslatorSkeleton {

    private Language language;

    public Translator() {
        super();
        this.language = null;
    }

    @Override
    public Language getLanguage() {
        return this.language;
    }

    @Override
    public void translate(Reader reader) throws TranslationException {
        Lexer lexer = new Lexer(new PushbackReader(reader, 1024));
        Parser parser = new Parser(lexer);
        try {
            Start tree = parser.parse();
            this.translate(tree);
        }
        catch (LexerException e) {
            ParseError pe = new ParseError(ParseError.ERROR);
            pe.setMessage("Lexer exception: " + e.getMessage());
            this.getErrors().add(pe);
        }
        catch (ParserException e) {
            ParseError pe = new ParseError(ParseError.ERROR);
            Token t = e.getToken();
            pe.setToken(t.toString().trim());
            pe.setPosition(t.getLine(), t.getPos());
            pe.setMessage("Parser: " + e.getMessage());
            this.getErrors().add(pe);
        } catch (IOException e) {
            throw new TranslationException(e);
        }
        if (this.getErrors().getMaxLevel() >= ParseError.ERROR) {
            this.setState(null);
        }
    }

    protected void translate(Start tree) {
        GetSignaturePass sPass = new GetSignaturePass();
        sPass.setErrors(this.getErrors());
        tree.apply(sPass);
        if (this.getErrors().getMaxLevel() >= ParseError.ERROR) {
            this.setState(null);
            return;
        }
        final Set<String> funs = sPass.getFuns();
        final Map<String, List<String>> sorts = sPass.getSortMap();
        final Set<String> defs = sPass.getDefs();
        final Map<String, Set<Integer>> mu = sPass.getMu();

        CreateBuiltinPass cPass = new CreateBuiltinPass(funs, sorts, defs);
        cPass.setErrors(this.getErrors());
        tree.apply(cPass);
        if (this.getErrors().getMaxLevel() >= ParseError.ERROR) {
            this.setState(null);
            return;
        }
        final Set<Rule> S = cPass.getS();
        final Set<Equation> E = cPass.getE();
        final Map<String, ImmutableList<String>> sortss = this.makeImmutable(sorts);

        RulePass rPass = new RulePass(sorts);
        rPass.setErrors(this.getErrors());
        tree.apply(rPass);
        if (this.getErrors().getMaxLevel() >= ParseError.ERROR) {
            this.setState(null);
            return;
        }
        final Set<PARule> R = rPass.getR();

        this.setState(
            PATRSProblem.create(
                ImmutableCreator.create(R),
                ImmutableCreator.create(S),
                ImmutableCreator.create(E),
                ImmutableCreator.create(sortss)
            )
        );
        this.language = Language.PATRS;

        if (!mu.keySet().isEmpty()) {
            this.complete(mu, (PATRSProblem) this.getState());
            Map<String, ImmutableSet<Integer>> muu = this.makeImmutableSet(mu);
            this.setState(
                CSPATRSProblem.create(
                    ImmutableCreator.create(R),
                    ImmutableCreator.create(S),
                    ImmutableCreator.create(E),
                    ImmutableCreator.create(sortss),
                    ImmutableCreator.create(muu)
                )
            );
            this.language = Language.CSPATRS;
        }
    }

    private void complete(Map<String, Set<Integer>> mu, PATRSProblem patrs) {
        Set<Integer> one = new LinkedHashSet<Integer>();
        Set<Integer> onetwo = new LinkedHashSet<Integer>();
        one.add(Integer.valueOf(0));
        onetwo.add(Integer.valueOf(0));
        onetwo.add(Integer.valueOf(1));

        mu.put("0", new LinkedHashSet<Integer>());
        mu.put("1", new LinkedHashSet<Integer>());
        mu.put("-", one);
        mu.put("+", onetwo);

        for (FunctionSymbol f : patrs.getSignature()) {
            String name = f.getName();
            if (mu.get(name) == null) {
                // full
                Set<Integer> tmp = new LinkedHashSet<Integer>();
                int arr = f.getArity();
                for (int i = 0; i < arr; i++) {
                    tmp.add(Integer.valueOf(i));
                }
                mu.put(f.getName(), tmp);
            }
        }
    }

    private Map<String, ImmutableList<String>> makeImmutable(Map<String, List<String>> inp) {
        Map<String, ImmutableList<String>> res = new LinkedHashMap<String, ImmutableList<String>>();
        for (String o : inp.keySet()) {
            res.put(o, ImmutableCreator.create(inp.get(o)));
        }
        return res;
    }

    private Map<String, ImmutableSet<Integer>> makeImmutableSet(Map<String, Set<Integer>> inp) {
        Map<String, ImmutableSet<Integer>> res = new LinkedHashMap<String, ImmutableSet<Integer>>();
        for (String o : inp.keySet()) {
            res.put(o, ImmutableCreator.create(inp.get(o)));
        }
        return res;
    }

}
